import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1459 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1459)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 1 2 (meaning1426 q) (meaning1450 q) (meaning1459 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1450 = false ∨ valuation q 1459 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1460 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1460)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 1 3 (meaning1426 q) (meaning1451 q) (meaning1460 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1451 = false ∨ valuation q 1460 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1461)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 1 4 (meaning1426 q) (meaning1452 q) (meaning1461 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1452 = false ∨ valuation q 1461 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1459)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 2 1 (meaning1427 q) (meaning1449 q) (meaning1459 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1449 = false ∨ valuation q 1459 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1460 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1460)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 2 2 (meaning1427 q) (meaning1450 q) (meaning1460 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1450 = false ∨ valuation q 1460 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1461)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 2 3 (meaning1427 q) (meaning1451 q) (meaning1461 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1451 = false ∨ valuation q 1461 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1462)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 2 4 (meaning1427 q) (meaning1452 q) (meaning1462 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1452 = false ∨ valuation q 1462 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1460 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1460)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 3 1 (meaning1428 q) (meaning1449 q) (meaning1460 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1449 = false ∨ valuation q 1460 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1461)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 3 2 (meaning1428 q) (meaning1450 q) (meaning1461 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1450 = false ∨ valuation q 1461 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1462)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 3 3 (meaning1428 q) (meaning1451 q) (meaning1462 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1451 = false ∨ valuation q 1462 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1463)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 3 4 (meaning1428 q) (meaning1452 q) (meaning1463 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1452 = false ∨ valuation q 1463 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1461)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 4 1 (meaning1429 q) (meaning1449 q) (meaning1461 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1449 = false ∨ valuation q 1461 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1462)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 4 2 (meaning1429 q) (meaning1450 q) (meaning1462 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1450 = false ∨ valuation q 1462 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1462)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 5 1 (meaning1430 q) (meaning1449 q) (meaning1462 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1449 = false ∨ valuation q 1462 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-3, -4, -6, -8, -10, -12, -13]) + (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13]) (l₂ := [-15, -18, -19, -21, -24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1464)) (countLit q [-3, -4, -6, -8, -10, -12, -13]) (countLit q [-15, -18, -19, -21, -24, -26, -28, -29]) (count1457 q) 5 3 (meaning1430 q) (meaning1451 q) (meaning1464 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1451 = false ∨ valuation q 1464 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1472)) (countLit q [-34]) (countLit q [-35]) (count1472 q) 1 (meaningNeg35 q) (meaning1472 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1472 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1472)) (countLit q [-34]) (countLit q [-35]) (count1472 q) 1 (meaningNeg34 q) (meaning1472 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1472 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1473)) (countLit q [-34]) (countLit q [-35]) (count1472 q) 1 1 (meaningNeg34 q) (meaningNeg35 q) (meaning1473 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 1473 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 1 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 2 (meaning1473 q) (meaning1475 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1474)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 1 (meaningNeg31 q) (meaning1474 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1474 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 1 1 (meaningNeg31 q) (meaning1472 q) (meaning1475 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1477)) (countLit q [-37]) (countLit q [-39]) (count1477 q) 1 (meaningNeg39 q) (meaning1477 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1477 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1477)) (countLit q [-37]) (countLit q [-39]) (count1477 q) 1 (meaningNeg37 q) (meaning1477 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1477 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1478)) (countLit q [-37]) (countLit q [-39]) (count1477 q) 1 1 (meaningNeg37 q) (meaningNeg39 q) (meaning1478 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 1478 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (1479)) (countLit q [-41]) (countLit q [-43]) (count1479 q) 1 (meaningNeg43 q) (meaning1479 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1479 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1479)) (countLit q [-41]) (countLit q [-43]) (count1479 q) 1 (meaningNeg41 q) (meaning1479 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1479 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 43 = true ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (1480)) (countLit q [-41]) (countLit q [-43]) (count1479 q) 1 1 (meaningNeg41 q) (meaningNeg43 q) (meaning1480 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 1480 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-37, -39]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-41, -43])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1481)) (countLit q [-37, -39]) (countLit q [-41, -43]) (count1481 q) 1 (meaning1479 q) (meaning1481 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1481 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-37, -39]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-41, -43])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (countLit q [-37, -39]) (countLit q [-41, -43]) (count1481 q) 2 (meaning1480 q) (meaning1482 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-37, -39]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-41, -43])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-37, -39]) (countLit q [-41, -43]) (count1481 q) 1 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-37, -39]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-41, -43])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1482)) (countLit q [-37, -39]) (countLit q [-41, -43]) (count1481 q) 1 1 (meaning1477 q) (meaning1479 q) (meaning1482 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = false ∨ valuation q 1482 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E096.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112096
