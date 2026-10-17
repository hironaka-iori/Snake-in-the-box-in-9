import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1452)) (countLit q [-10]) (countLit q [-11]) (count1452 q) 1 (meaningNeg11 q) (meaning1452 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1452 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1452)) (countLit q [-10]) (countLit q [-11]) (count1452 q) 1 (meaningNeg10 q) (meaning1452 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1452 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1454)) (countLit q [-12]) (countLit q [-13]) (count1454 q) 1 (meaningNeg13 q) (meaning1454 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1454 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1454)) (countLit q [-12]) (countLit q [-13]) (count1454 q) 1 (meaningNeg12 q) (meaning1454 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1454 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1455)) (countLit q [-12]) (countLit q [-13]) (count1454 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1455 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1455 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-10, -11]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1456)) (countLit q [-10, -11]) (countLit q [-12, -13]) (count1456 q) 1 (meaning1454 q) (meaning1456 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1456 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-10, -11]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1457)) (countLit q [-10, -11]) (countLit q [-12, -13]) (count1456 q) 2 (meaning1455 q) (meaning1457 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1457 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-10, -11]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-10, -11]) (countLit q [-12, -13]) (count1456 q) 1 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-10, -11]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1457)) (countLit q [-10, -11]) (countLit q [-12, -13]) (count1456 q) 1 1 (meaning1452 q) (meaning1454 q) (meaning1457 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1454 = false ∨ valuation q 1457 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -6]) + (countLit q [-10, -11, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-10, -11, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1460)) (countLit q [-2, -4, -6]) (countLit q [-10, -11, -12, -13]) (count1460 q) 1 (meaning1456 q) (meaning1460 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1460 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -6]) + (countLit q [-10, -11, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-10, -11, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -6]) (countLit q [-10, -11, -12, -13]) (count1460 q) 2 (meaning1457 q) (meaning1461 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1461 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -6]) + (countLit q [-10, -11, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6]) (l₂ := [-10, -11, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -6]) (countLit q [-10, -11, -12, -13]) (count1460 q) 1 1 (meaning1449 q) (meaning1456 q) (meaning1461 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1456 = false ∨ valuation q 1461 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1467)) (countLit q [-21]) (countLit q [-23]) (count1467 q) 1 (meaningNeg23 q) (meaning1467 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1467 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1467)) (countLit q [-21]) (countLit q [-23]) (count1467 q) 1 (meaningNeg21 q) (meaning1467 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1467 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1468)) (countLit q [-21]) (countLit q [-23]) (count1467 q) 1 1 (meaningNeg21 q) (meaningNeg23 q) (meaning1468 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 1468 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-17]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-21, -23])
  have hm := merge_right (literal (valuationOf q) (1467)) (literal (valuationOf q) (1469)) (countLit q [-17]) (countLit q [-21, -23]) (count1469 q) 1 (meaning1467 q) (meaning1469 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1469 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1470 = true := by
  have hs : count1469 q = (countLit q [-17]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-21, -23])
  have hm := merge_right (literal (valuationOf q) (1468)) (literal (valuationOf q) (1470)) (countLit q [-17]) (countLit q [-21, -23]) (count1469 q) 2 (meaning1468 q) (meaning1470 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1470 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-17]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-21, -23])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1469)) (countLit q [-17]) (countLit q [-21, -23]) (count1469 q) 1 (meaningNeg17 q) (meaning1469 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1469 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1467 = false ∨ valuationOf q 1470 = true := by
  have hs : count1469 q = (countLit q [-17]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-21, -23])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1470)) (countLit q [-17]) (countLit q [-21, -23]) (count1469 q) 1 1 (meaningNeg17 q) (meaning1467 q) (meaning1470 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1467 = false ∨ valuation q 1470 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1472)) (countLit q [-24]) (countLit q [-25]) (count1472 q) 1 (meaningNeg25 q) (meaning1472 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1472 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1472)) (countLit q [-24]) (countLit q [-25]) (count1472 q) 1 (meaningNeg24 q) (meaning1472 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1472 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1473)) (countLit q [-24]) (countLit q [-25]) (count1472 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning1473 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 1473 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1474)) (countLit q [-29]) (countLit q [-31]) (count1474 q) 1 (meaningNeg31 q) (meaning1474 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1474 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1474)) (countLit q [-29]) (countLit q [-31]) (count1474 q) 1 (meaningNeg29 q) (meaning1474 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1474 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1475)) (countLit q [-29]) (countLit q [-31]) (count1474 q) 1 1 (meaningNeg29 q) (meaningNeg31 q) (meaning1475 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 1475 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-24, -25]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1476)) (countLit q [-24, -25]) (countLit q [-29, -31]) (count1476 q) 1 (meaning1474 q) (meaning1476 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1476 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-24, -25]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-24, -25]) (countLit q [-29, -31]) (count1476 q) 1 (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-24, -25]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1477)) (countLit q [-24, -25]) (countLit q [-29, -31]) (count1476 q) 1 1 (meaning1472 q) (meaning1474 q) (meaning1477 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = false ∨ valuation q 1477 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-24, -25]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (countLit q [-24, -25]) (countLit q [-29, -31]) (count1476 q) 1 2 (meaning1472 q) (meaning1475 q) (meaning1478 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1475 = false ∨ valuation q 1478 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-24, -25]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-24, -25]) (countLit q [-29, -31]) (count1476 q) 2 (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1477 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-24, -25]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-24, -25]) (countLit q [-29, -31]) (count1476 q) 2 1 (meaning1473 q) (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1474 = false ∨ valuation q 1478 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 1 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E187.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112187
