import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1472 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1472)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 5 6 (meaning1393 q) (meaning1452 q) (meaning1472 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1452 = false ∨ valuation q 1472 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1473 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1473)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 5 7 (meaning1393 q) (meaning1453 q) (meaning1473 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1453 = false ∨ valuation q 1473 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1474 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1474)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 5 8 (meaning1393 q) (meaning1454 q) (meaning1474 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1454 = false ∨ valuation q 1474 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1475 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1475)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 5 9 (meaning1393 q) (meaning1455 q) (meaning1475 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1455 = false ∨ valuation q 1475 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1471 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1471)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 6 4 (meaning1394 q) (meaning1450 q) (meaning1471 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1450 = false ∨ valuation q 1471 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1472 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1472)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 6 5 (meaning1394 q) (meaning1451 q) (meaning1472 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1451 = false ∨ valuation q 1472 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1473 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1473)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 6 6 (meaning1394 q) (meaning1452 q) (meaning1473 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1452 = false ∨ valuation q 1473 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1474 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1474)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 6 7 (meaning1394 q) (meaning1453 q) (meaning1474 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1453 = false ∨ valuation q 1474 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1475 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1475)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 6 8 (meaning1394 q) (meaning1454 q) (meaning1475 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1454 = false ∨ valuation q 1475 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1472 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1472)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 7 4 (meaning1395 q) (meaning1450 q) (meaning1472 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1450 = false ∨ valuation q 1472 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1473 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1473)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 7 5 (meaning1395 q) (meaning1451 q) (meaning1473 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1451 = false ∨ valuation q 1473 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1474 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1474)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 7 6 (meaning1395 q) (meaning1452 q) (meaning1474 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1452 = false ∨ valuation q 1474 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1475 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1475)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 7 7 (meaning1395 q) (meaning1453 q) (meaning1475 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1453 = false ∨ valuation q 1475 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1473 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1473)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 8 4 (meaning1396 q) (meaning1450 q) (meaning1473 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1450 = false ∨ valuation q 1473 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1474 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1474)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 8 5 (meaning1396 q) (meaning1451 q) (meaning1474 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1451 = false ∨ valuation q 1474 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1475 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1475)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 8 6 (meaning1396 q) (meaning1452 q) (meaning1475 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1452 = false ∨ valuation q 1475 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1475 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1397)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1475)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 9 5 (meaning1397 q) (meaning1451 q) (meaning1475 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1451 = false ∨ valuation q 1475 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1476 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1397)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1476)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 9 6 (meaning1397 q) (meaning1452 q) (meaning1476 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1452 = false ∨ valuation q 1476 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1481)) (countLit q [-59]) (countLit q [-60]) (count1481 q) 1 (meaningNeg60 q) (meaning1481 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1481 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1481)) (countLit q [-59]) (countLit q [-60]) (count1481 q) 1 (meaningNeg59 q) (meaning1481 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1481 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 60 = true ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (1482)) (countLit q [-59]) (countLit q [-60]) (count1481 q) 1 1 (meaningNeg59 q) (meaningNeg60 q) (meaning1482 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 1482 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1483)) (countLit q [-56]) (countLit q [-59, -60]) (count1483 q) 1 (meaning1481 q) (meaning1483 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1483 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1484 = true := by
  have hs : count1483 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1484)) (countLit q [-56]) (countLit q [-59, -60]) (count1483 q) 2 (meaning1482 q) (meaning1484 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1483)) (countLit q [-56]) (countLit q [-59, -60]) (count1483 q) 1 (meaningNeg56 q) (meaning1483 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1483 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1481 = false ∨ valuationOf q 1484 = true := by
  have hs : count1483 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1484)) (countLit q [-56]) (countLit q [-59, -60]) (count1483 q) 1 1 (meaningNeg56 q) (meaning1481 q) (meaning1484 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1481 = false ∨ valuation q 1484 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true := by
  have hs : count1483 q = (countLit q [-56]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1485)) (countLit q [-56]) (countLit q [-59, -60]) (count1483 q) 1 2 (meaningNeg56 q) (meaning1482 q) (meaning1485 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1482 = false ∨ valuation q 1485 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1486 = true := by
  have hs : count1486 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1486)) (countLit q [-64]) (countLit q [-65]) (count1486 q) 1 (meaningNeg64 q) (meaning1486 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1486 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1488)) (countLit q [-67]) (countLit q [-69]) (count1488 q) 1 (meaningNeg69 q) (meaning1488 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1488 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1488)) (countLit q [-67]) (countLit q [-69]) (count1488 q) 1 (meaningNeg67 q) (meaning1488 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1488 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-64, -65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -69])
  have hm := merge_right (literal (valuationOf q) (1488)) (literal (valuationOf q) (1490)) (countLit q [-64, -65]) (countLit q [-67, -69]) (count1490 q) 1 (meaning1488 q) (meaning1490 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1490 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-64, -65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -69])
  have hm := merge_left (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-64, -65]) (countLit q [-67, -69]) (count1490 q) 1 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1491 = true := by
  have hs : count1490 q = (countLit q [-64, -65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -69])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1491)) (countLit q [-64, -65]) (countLit q [-67, -69]) (count1490 q) 1 1 (meaning1486 q) (meaning1488 q) (meaning1491 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1488 = false ∨ valuation q 1491 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E146.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112146
