import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1527 = true := by
  have hs : count1527 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1527)) (countLit q [-26]) (countLit q [-28]) (count1527 q) 1 (meaningNeg28 q) (meaning1527 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1527 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1527 = true := by
  have hs : count1527 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1527)) (countLit q [-26]) (countLit q [-28]) (count1527 q) 1 (meaningNeg26 q) (meaning1527 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1527 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 28 = true ∨ valuationOf q 1528 = true := by
  have hs : count1527 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (1528)) (countLit q [-26]) (countLit q [-28]) (count1527 q) 1 1 (meaningNeg26 q) (meaningNeg28 q) (meaning1528 q) hs
  change (! (valuationOf q 26)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 1528 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-22, -25]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (countLit q [-22, -25]) (countLit q [-26, -28]) (count1529 q) 1 (meaning1527 q) (meaning1529 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-22, -25]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (countLit q [-22, -25]) (countLit q [-26, -28]) (count1529 q) 2 (meaning1528 q) (meaning1530 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-22, -25]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1529)) (countLit q [-22, -25]) (countLit q [-26, -28]) (count1529 q) 1 (meaning1525 q) (meaning1529 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1529 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-22, -25]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1530)) (countLit q [-22, -25]) (countLit q [-26, -28]) (count1529 q) 1 1 (meaning1525 q) (meaning1527 q) (meaning1530 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1527 = false ∨ valuation q 1530 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true := by
  have hs : count1529 q = (countLit q [-22, -25]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (countLit q [-22, -25]) (countLit q [-26, -28]) (count1529 q) 1 2 (meaning1525 q) (meaning1528 q) (meaning1531 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1528 = false ∨ valuation q 1531 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-22, -25]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-22, -25]) (countLit q [-26, -28]) (count1529 q) 2 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 1 (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 2 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 3 (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1535 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1533)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 1 (meaning1521 q) (meaning1533 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1533 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1534)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 1 1 (meaning1521 q) (meaning1529 q) (meaning1534 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1529 = false ∨ valuation q 1534 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1535)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 1 2 (meaning1521 q) (meaning1530 q) (meaning1535 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1530 = false ∨ valuation q 1535 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1522)) (literal (valuationOf q) (1534)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 2 (meaning1522 q) (meaning1534 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1534 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1535)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 2 1 (meaning1522 q) (meaning1529 q) (meaning1535 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1529 = false ∨ valuation q 1535 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1536 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1536)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 2 2 (meaning1522 q) (meaning1530 q) (meaning1536 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1530 = false ∨ valuation q 1536 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1537 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1537)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 2 3 (meaning1522 q) (meaning1531 q) (meaning1537 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1531 = false ∨ valuation q 1537 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1523)) (literal (valuationOf q) (1535)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 3 (meaning1523 q) (meaning1535 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1535 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1536 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1536)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 3 1 (meaning1523 q) (meaning1529 q) (meaning1536 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1529 = false ∨ valuation q 1536 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1537 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1537)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 3 2 (meaning1523 q) (meaning1530 q) (meaning1537 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1530 = false ∨ valuation q 1537 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1536 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1524)) (literal (valuationOf q) (1536)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 4 (meaning1524 q) (meaning1536 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1536 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1537 = true := by
  have hs : count1533 q = (countLit q [-15, -16, -17, -19]) + (countLit q [-22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -17, -19]) (l₂ := [-22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1537)) (countLit q [-15, -16, -17, -19]) (countLit q [-22, -25, -26, -28]) (count1533 q) 4 1 (meaning1524 q) (meaning1529 q) (meaning1537 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1529 = false ∨ valuation q 1537 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1543)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 2 1 (meaning1511 q) (meaning1533 q) (meaning1543 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1533 = false ∨ valuation q 1543 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1544)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 2 2 (meaning1511 q) (meaning1534 q) (meaning1544 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1534 = false ∨ valuation q 1544 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1545)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 2 3 (meaning1511 q) (meaning1535 q) (meaning1545 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1535 = false ∨ valuation q 1545 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1546)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 2 4 (meaning1511 q) (meaning1536 q) (meaning1546 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1536 = false ∨ valuation q 1546 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1544)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 3 1 (meaning1512 q) (meaning1533 q) (meaning1544 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1533 = false ∨ valuation q 1544 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1545)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 3 2 (meaning1512 q) (meaning1534 q) (meaning1545 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1534 = false ∨ valuation q 1545 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1546)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 3 3 (meaning1512 q) (meaning1535 q) (meaning1546 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1535 = false ∨ valuation q 1546 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-1, -3, -5, -6, -8, -10, -13]) + (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13]) (l₂ := [-15, -16, -17, -19, -22, -25, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1547)) (countLit q [-1, -3, -5, -6, -8, -10, -13]) (countLit q [-15, -16, -17, -19, -22, -25, -26, -28]) (count1541 q) 3 4 (meaning1512 q) (meaning1536 q) (meaning1547 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1536 = false ∨ valuation q 1547 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E186.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112186
