import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1491)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 2 3 (meaning1457 q) (meaning1481 q) (meaning1491 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1481 = false ∨ valuation q 1491 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1492)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 2 4 (meaning1457 q) (meaning1482 q) (meaning1492 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1482 = false ∨ valuation q 1492 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1493)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 2 5 (meaning1457 q) (meaning1483 q) (meaning1493 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1483 = false ∨ valuation q 1493 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 3 1 (meaning1458 q) (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1479 = false ∨ valuation q 1490 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 3 2 (meaning1458 q) (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1480 = false ∨ valuation q 1491 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1492)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 3 3 (meaning1458 q) (meaning1481 q) (meaning1492 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1481 = false ∨ valuation q 1492 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1493 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1493)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 3 4 (meaning1458 q) (meaning1482 q) (meaning1493 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1482 = false ∨ valuation q 1493 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1494)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 3 5 (meaning1458 q) (meaning1483 q) (meaning1494 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1483 = false ∨ valuation q 1494 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1495 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1495)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 3 6 (meaning1458 q) (meaning1484 q) (meaning1495 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1484 = false ∨ valuation q 1495 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1491)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 4 1 (meaning1459 q) (meaning1479 q) (meaning1491 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1479 = false ∨ valuation q 1491 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1492)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 4 2 (meaning1459 q) (meaning1480 q) (meaning1492 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1480 = false ∨ valuation q 1492 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1493)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 4 3 (meaning1459 q) (meaning1481 q) (meaning1493 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1481 = false ∨ valuation q 1493 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1494 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1494)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 4 4 (meaning1459 q) (meaning1482 q) (meaning1494 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1482 = false ∨ valuation q 1494 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1495 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1495)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 4 5 (meaning1459 q) (meaning1483 q) (meaning1495 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1483 = false ∨ valuation q 1495 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1496 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1496)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 4 6 (meaning1459 q) (meaning1484 q) (meaning1496 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1484 = false ∨ valuation q 1496 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1494 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1494)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 5 3 (meaning1460 q) (meaning1481 q) (meaning1494 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1481 = false ∨ valuation q 1494 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1495 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1495)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 5 4 (meaning1460 q) (meaning1482 q) (meaning1495 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1482 = false ∨ valuation q 1495 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1496 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1496)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 5 5 (meaning1460 q) (meaning1483 q) (meaning1496 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1483 = false ∨ valuation q 1496 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1502)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 (meaningNeg31 q) (meaning1502 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1502 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1502)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 (meaningNeg28 q) (meaning1502 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1502 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1503)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 1 (meaningNeg28 q) (meaningNeg31 q) (meaning1503 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 1503 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1504)) (countLit q [-33]) (countLit q [-35]) (count1504 q) 1 (meaningNeg35 q) (meaning1504 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1504 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1504)) (countLit q [-33]) (countLit q [-35]) (count1504 q) 1 (meaningNeg33 q) (meaning1504 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1504 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1505)) (countLit q [-33]) (countLit q [-35]) (count1504 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning1505 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 1505 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 (meaning1504 q) (meaning1506 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 1 (meaning1502 q) (meaning1504 q) (meaning1507 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = false ∨ valuation q 1507 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 1 2 (meaning1502 q) (meaning1505 q) (meaning1508 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1507 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 1 (meaning1503 q) (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1504 = false ∨ valuation q 1508 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1506 q = (countLit q [-28, -31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-28, -31]) (countLit q [-33, -35]) (count1506 q) 2 2 (meaning1503 q) (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1505 = false ∨ valuation q 1509 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E024.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112024
