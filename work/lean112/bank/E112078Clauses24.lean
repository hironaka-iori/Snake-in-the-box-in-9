import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1464 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 3 2 (meaning1451 q) (meaning1457 q) (meaning1464 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1457 = false ∨ valuation q 1464 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1467)) (countLit q [-14]) (countLit q [-17]) (count1467 q) 1 (meaningNeg17 q) (meaning1467 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1467 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1467)) (countLit q [-14]) (countLit q [-17]) (count1467 q) 1 (meaningNeg14 q) (meaning1467 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1467 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1468)) (countLit q [-14]) (countLit q [-17]) (count1467 q) 1 1 (meaningNeg14 q) (meaningNeg17 q) (meaning1468 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 1468 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1467)) (literal (valuationOf q) (1469)) (countLit q [-13]) (countLit q [-14, -17]) (count1469 q) 1 (meaning1467 q) (meaning1469 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1469 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1470 = true := by
  have hs : count1469 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1468)) (literal (valuationOf q) (1470)) (countLit q [-13]) (countLit q [-14, -17]) (count1469 q) 2 (meaning1468 q) (meaning1470 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1470 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1469)) (countLit q [-13]) (countLit q [-14, -17]) (count1469 q) 1 (meaningNeg13 q) (meaning1469 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1469 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1467 = false ∨ valuationOf q 1470 = true := by
  have hs : count1469 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1470)) (countLit q [-13]) (countLit q [-14, -17]) (count1469 q) 1 1 (meaningNeg13 q) (meaning1467 q) (meaning1470 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1467 = false ∨ valuation q 1470 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1468 = false ∨ valuationOf q 1471 = true := by
  have hs : count1469 q = (countLit q [-13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1471)) (countLit q [-13]) (countLit q [-14, -17]) (count1469 q) 1 2 (meaningNeg13 q) (meaning1468 q) (meaning1471 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1468 = false ∨ valuation q 1471 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1472)) (countLit q [-20]) (countLit q [-22]) (count1472 q) 1 (meaningNeg22 q) (meaning1472 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1472 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1472)) (countLit q [-20]) (countLit q [-22]) (count1472 q) 1 (meaningNeg20 q) (meaning1472 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1472 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1473)) (countLit q [-20]) (countLit q [-22]) (count1472 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning1473 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 1473 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1474)) (countLit q [-25]) (countLit q [-26]) (count1474 q) 1 (meaningNeg26 q) (meaning1474 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1474 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1474)) (countLit q [-25]) (countLit q [-26]) (count1474 q) 1 (meaningNeg25 q) (meaning1474 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1474 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1475)) (countLit q [-25]) (countLit q [-26]) (count1474 q) 1 1 (meaningNeg25 q) (meaningNeg26 q) (meaning1475 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 1475 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 1 (meaning1474 q) (meaning1476 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1476 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1477)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 2 (meaning1475 q) (meaning1477 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1477 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 1 (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1477)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 1 1 (meaning1472 q) (meaning1474 q) (meaning1477 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = false ∨ valuation q 1477 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 1 2 (meaning1472 q) (meaning1475 q) (meaning1478 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1475 = false ∨ valuation q 1478 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 2 (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1477 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 2 1 (meaning1473 q) (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1474 = false ∨ valuation q 1478 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1476 q) 2 2 (meaning1473 q) (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = false ∨ valuation q 1479 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 1 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 2 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 3 (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1482 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 4 (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1483 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1480)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 1 (meaning1469 q) (meaning1480 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1480 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 1 1 (meaning1469 q) (meaning1476 q) (meaning1481 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1476 = false ∨ valuation q 1481 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 1 2 (meaning1469 q) (meaning1477 q) (meaning1482 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1477 = false ∨ valuation q 1482 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 1 3 (meaning1469 q) (meaning1478 q) (meaning1483 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1478 = false ∨ valuation q 1483 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 1 4 (meaning1469 q) (meaning1479 q) (meaning1484 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1479 = false ∨ valuation q 1484 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E078.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112078
