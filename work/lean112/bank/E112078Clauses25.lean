import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 2 (meaning1470 q) (meaning1481 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1481 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 2 1 (meaning1470 q) (meaning1476 q) (meaning1482 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1476 = false ∨ valuation q 1482 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1483 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 2 2 (meaning1470 q) (meaning1477 q) (meaning1483 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1477 = false ∨ valuation q 1483 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 2 3 (meaning1470 q) (meaning1478 q) (meaning1484 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1478 = false ∨ valuation q 1484 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1482 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 3 (meaning1471 q) (meaning1482 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1482 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1483 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 3 1 (meaning1471 q) (meaning1476 q) (meaning1483 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1476 = false ∨ valuation q 1483 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1484 = true := by
  have hs : count1480 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1484)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -25, -26]) (count1480 q) 3 2 (meaning1471 q) (meaning1477 q) (meaning1484 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1477 = false ∨ valuation q 1484 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1487)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 1 (meaning1480 q) (meaning1487 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1487 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1489 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1489)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 3 (meaning1482 q) (meaning1489 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1489 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1487)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 1 (meaning1460 q) (meaning1487 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1487 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1488)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 1 1 (meaning1460 q) (meaning1480 q) (meaning1488 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1480 = false ∨ valuation q 1488 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1489)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 1 2 (meaning1460 q) (meaning1481 q) (meaning1489 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1481 = false ∨ valuation q 1489 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1490 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 1 3 (meaning1460 q) (meaning1482 q) (meaning1490 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1482 = false ∨ valuation q 1490 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1491)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 1 4 (meaning1460 q) (meaning1483 q) (meaning1491 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1483 = false ∨ valuation q 1491 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1492)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 1 5 (meaning1460 q) (meaning1484 q) (meaning1492 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1484 = false ∨ valuation q 1492 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1488)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 2 (meaning1461 q) (meaning1488 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1488 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 2 1 (meaning1461 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 2 2 (meaning1461 q) (meaning1481 q) (meaning1490 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1481 = false ∨ valuation q 1490 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 2 3 (meaning1461 q) (meaning1482 q) (meaning1491 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1482 = false ∨ valuation q 1491 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1492)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 2 4 (meaning1461 q) (meaning1483 q) (meaning1492 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1483 = false ∨ valuation q 1492 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1493 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1493)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 2 5 (meaning1461 q) (meaning1484 q) (meaning1493 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1484 = false ∨ valuation q 1493 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1489 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1489)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 3 (meaning1462 q) (meaning1489 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1489 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 3 1 (meaning1462 q) (meaning1480 q) (meaning1490 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1480 = false ∨ valuation q 1490 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1491)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 3 2 (meaning1462 q) (meaning1481 q) (meaning1491 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1481 = false ∨ valuation q 1491 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1492)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 3 3 (meaning1462 q) (meaning1482 q) (meaning1492 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1482 = false ∨ valuation q 1492 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1493)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 3 4 (meaning1462 q) (meaning1483 q) (meaning1493 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1483 = false ∨ valuation q 1493 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1494 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1494)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 3 5 (meaning1462 q) (meaning1484 q) (meaning1494 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1484 = false ∨ valuation q 1494 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1490 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 4 (meaning1463 q) (meaning1490 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1490 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 4 1 (meaning1463 q) (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1480 = false ∨ valuation q 1491 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1492)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 4 2 (meaning1463 q) (meaning1481 q) (meaning1492 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1481 = false ∨ valuation q 1492 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1493 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1493)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 4 3 (meaning1463 q) (meaning1482 q) (meaning1493 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1482 = false ∨ valuation q 1493 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1494)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 4 4 (meaning1463 q) (meaning1483 q) (meaning1494 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1483 = false ∨ valuation q 1494 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E078.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112078
