import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec60 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1921 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1641)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 2 3 (meaning1622 q) (meaning1634 q) (meaning1641 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1921 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1634 = false ∨ valuation q 1641 = true := counterClause1921 (baseVal q)

theorem counterClause1922 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1640)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 3 1 (meaning1623 q) (meaning1632 q) (meaning1640 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1922 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1632 = false ∨ valuation q 1640 = true := counterClause1922 (baseVal q)

theorem counterClause1923 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1641)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 3 2 (meaning1623 q) (meaning1633 q) (meaning1641 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1923 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1633 = false ∨ valuation q 1641 = true := counterClause1923 (baseVal q)

theorem counterClause1924 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 3 3 (meaning1623 q) (meaning1634 q) (meaning1642 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1924 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1634 = false ∨ valuation q 1642 = true := counterClause1924 (baseVal q)

theorem counterClause1925 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1638)) (literal (valuationOf q) (1647)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 2 (meaning1638 q) (meaning1647 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1925 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1647 = true := counterClause1925 (baseVal q)

theorem counterClause1926 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1648)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 3 (meaning1639 q) (meaning1648 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1926 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1648 = true := counterClause1926 (baseVal q)

theorem counterClause1927 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1649)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 4 (meaning1640 q) (meaning1649 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1927 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1649 = true := counterClause1927 (baseVal q)

theorem counterClause1928 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1648)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 1 2 (meaning1609 q) (meaning1638 q) (meaning1648 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1928 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1638 = false ∨ valuation q 1648 = true := counterClause1928 (baseVal q)

theorem counterClause1929 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1649)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 1 3 (meaning1609 q) (meaning1639 q) (meaning1649 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1929 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1639 = false ∨ valuation q 1649 = true := counterClause1929 (baseVal q)

theorem counterClause1930 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1650)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 1 4 (meaning1609 q) (meaning1640 q) (meaning1650 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1930 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1640 = false ∨ valuation q 1650 = true := counterClause1930 (baseVal q)

theorem counterClause1931 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1651)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 1 5 (meaning1609 q) (meaning1641 q) (meaning1651 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1931 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1641 = false ∨ valuation q 1651 = true := counterClause1931 (baseVal q)

theorem counterClause1932 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1648)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 2 1 (meaning1610 q) (meaning1637 q) (meaning1648 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1932 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1637 = false ∨ valuation q 1648 = true := counterClause1932 (baseVal q)

theorem counterClause1933 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1649)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 2 2 (meaning1610 q) (meaning1638 q) (meaning1649 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1933 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1638 = false ∨ valuation q 1649 = true := counterClause1933 (baseVal q)

theorem counterClause1934 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1650)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 2 3 (meaning1610 q) (meaning1639 q) (meaning1650 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1934 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1639 = false ∨ valuation q 1650 = true := counterClause1934 (baseVal q)

theorem counterClause1935 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1651)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 2 4 (meaning1610 q) (meaning1640 q) (meaning1651 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1935 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1640 = false ∨ valuation q 1651 = true := counterClause1935 (baseVal q)

theorem counterClause1936 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1652)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 2 5 (meaning1610 q) (meaning1641 q) (meaning1652 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1936 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1641 = false ∨ valuation q 1652 = true := counterClause1936 (baseVal q)

theorem counterClause1937 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1649)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 3 1 (meaning1611 q) (meaning1637 q) (meaning1649 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1937 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1637 = false ∨ valuation q 1649 = true := counterClause1937 (baseVal q)

theorem counterClause1938 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1650)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 3 2 (meaning1611 q) (meaning1638 q) (meaning1650 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1938 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1638 = false ∨ valuation q 1650 = true := counterClause1938 (baseVal q)

theorem counterClause1939 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1651)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 3 3 (meaning1611 q) (meaning1639 q) (meaning1651 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1939 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1639 = false ∨ valuation q 1651 = true := counterClause1939 (baseVal q)

theorem counterClause1940 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1652)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 3 4 (meaning1611 q) (meaning1640 q) (meaning1652 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1940 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1640 = false ∨ valuation q 1652 = true := counterClause1940 (baseVal q)

theorem counterClause1941 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1653 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1653)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 3 5 (meaning1611 q) (meaning1641 q) (meaning1653 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1941 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1641 = false ∨ valuation q 1653 = true := counterClause1941 (baseVal q)

theorem counterClause1942 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1654 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1654)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 3 6 (meaning1611 q) (meaning1642 q) (meaning1654 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1942 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1642 = false ∨ valuation q 1654 = true := counterClause1942 (baseVal q)

theorem counterClause1943 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1650)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 4 1 (meaning1612 q) (meaning1637 q) (meaning1650 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1943 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1637 = false ∨ valuation q 1650 = true := counterClause1943 (baseVal q)

theorem counterClause1944 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1651)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 4 2 (meaning1612 q) (meaning1638 q) (meaning1651 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1944 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1638 = false ∨ valuation q 1651 = true := counterClause1944 (baseVal q)

theorem counterClause1945 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1652)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 4 3 (meaning1612 q) (meaning1639 q) (meaning1652 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1945 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1639 = false ∨ valuation q 1652 = true := counterClause1945 (baseVal q)

theorem counterClause1946 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1653 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1653)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 4 4 (meaning1612 q) (meaning1640 q) (meaning1653 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1946 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1640 = false ∨ valuation q 1653 = true := counterClause1946 (baseVal q)

theorem counterClause1947 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1651)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 5 1 (meaning1613 q) (meaning1637 q) (meaning1651 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1947 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1637 = false ∨ valuation q 1651 = true := counterClause1947 (baseVal q)

theorem counterClause1948 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1652)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 5 2 (meaning1613 q) (meaning1638 q) (meaning1652 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1948 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1638 = false ∨ valuation q 1652 = true := counterClause1948 (baseVal q)

theorem counterClause1949 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1654 = true := by
  have hs : count1646 q = (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) + (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38, -39, -41, -43, -45]) (l₂ := [-47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1654)) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45]) (countLit q [-47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1646 q) 5 4 (meaning1613 q) (meaning1640 q) (meaning1654 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1949 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1640 = false ∨ valuation q 1654 = true := counterClause1949 (baseVal q)

theorem counterClause1950 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1672 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 3 7 (meaning1579 q) (meaning1652 q) (meaning1672 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1950 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1652 = false ∨ valuation q 1672 = true := counterClause1950 (baseVal q)

theorem counterClause1951 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1672 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 4 6 (meaning1580 q) (meaning1651 q) (meaning1672 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1951 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1651 = false ∨ valuation q 1672 = true := counterClause1951 (baseVal q)

theorem counterClause1952 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) + (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (l₂ := [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31]) (countLit q [-33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (count1663 q) 5 5 (meaning1581 q) (meaning1650 q) (meaning1672 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1952 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1650 = false ∨ valuation q 1672 = true := counterClause1952 (baseVal q)

theorem block60 (q : Snake 81) (h : Conditions q) : B112E260.Block60 (valuation q) :=
  ⟨clause1921 q h, clause1922 q h, clause1923 q h, clause1924 q h, clause1925 q h, clause1926 q h, clause1927 q h, clause1928 q h, clause1929 q h, clause1930 q h, clause1931 q h, clause1932 q h, clause1933 q h, clause1934 q h, clause1935 q h, clause1936 q h, clause1937 q h, clause1938 q h, clause1939 q h, clause1940 q h, clause1941 q h, clause1942 q h, clause1943 q h, clause1944 q h, clause1945 q h, clause1946 q h, clause1947 q h, clause1948 q h, clause1949 q h, clause1950 q h, clause1951 q h, clause1952 q h⟩

end
end Snake9.Regrowth.E112260
