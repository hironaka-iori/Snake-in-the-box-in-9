import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec59 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1889 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1639)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1638 q) 2 (meaning1635 q) (meaning1639 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1889 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1639 = true := counterClause1889 (baseVal q)

theorem counterClause1890 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1642)) (countLit q [-55]) (countLit q [-57]) (count1642 q) 1 (meaningNeg57 q) (meaning1642 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1890 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1642 = true := counterClause1890 (baseVal q)

theorem counterClause1891 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1643)) (countLit q [-55]) (countLit q [-57]) (count1642 q) 1 1 (meaningNeg55 q) (meaningNeg57 q) (meaning1643 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1891 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 1643 = true := counterClause1891 (baseVal q)

theorem counterClause1892 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-58]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1644)) (countLit q [-58]) (countLit q [-62]) (count1644 q) 1 (meaningNeg62 q) (meaning1644 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1892 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1644 = true := counterClause1892 (baseVal q)

theorem counterClause1893 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-58]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1644)) (countLit q [-58]) (countLit q [-62]) (count1644 q) 1 (meaningNeg58 q) (meaning1644 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1893 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1644 = true := counterClause1893 (baseVal q)

theorem counterClause1894 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_left (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1646 q) 1 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1894 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1894 (baseVal q)

theorem counterClause1895 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1647)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1646 q) 1 1 (meaning1642 q) (meaning1644 q) (meaning1647 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1895 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1644 = false ∨ valuation q 1647 = true := counterClause1895 (baseVal q)

theorem counterClause1896 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1646 q) 2 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1896 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1896 (baseVal q)

theorem counterClause1897 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1646 q) 2 1 (meaning1643 q) (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1897 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1897 (baseVal q)

theorem counterClause1898 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_right (literal (valuationOf q) (1647)) (literal (valuationOf q) (1651)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1650 q) 2 (meaning1647 q) (meaning1651 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1898 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1651 = true := counterClause1898 (baseVal q)

theorem counterClause1899 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1652 = true := by
  have hs : count1650 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_right (literal (valuationOf q) (1648)) (literal (valuationOf q) (1652)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1650 q) 3 (meaning1648 q) (meaning1652 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1899 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1652 = true := counterClause1899 (baseVal q)

theorem counterClause1900 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1651)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1650 q) 1 1 (meaning1638 q) (meaning1646 q) (meaning1651 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1900 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1646 = false ∨ valuation q 1651 = true := counterClause1900 (baseVal q)

theorem counterClause1901 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1652 = true := by
  have hs : count1650 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1652)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1650 q) 1 2 (meaning1638 q) (meaning1647 q) (meaning1652 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1901 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1647 = false ∨ valuation q 1652 = true := counterClause1901 (baseVal q)

theorem counterClause1902 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1639)) (literal (valuationOf q) (1651)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1650 q) 2 (meaning1639 q) (meaning1651 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1902 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1651 = true := counterClause1902 (baseVal q)

theorem counterClause1903 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1652 = true := by
  have hs : count1650 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1652)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1650 q) 2 1 (meaning1639 q) (meaning1646 q) (meaning1652 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1903 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1646 = false ∨ valuation q 1652 = true := counterClause1903 (baseVal q)

theorem counterClause1904 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true := by
  have hs : count1658 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1661)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1658 q) 2 2 (meaning1627 q) (meaning1651 q) (meaning1661 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1904 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1651 = false ∨ valuation q 1661 = true := counterClause1904 (baseVal q)

theorem counterClause1905 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true := by
  have hs : count1658 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1662)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1658 q) 2 3 (meaning1627 q) (meaning1652 q) (meaning1662 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1905 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1652 = false ∨ valuation q 1662 = true := counterClause1905 (baseVal q)

theorem counterClause1906 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true := by
  have hs : count1658 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1662)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1658 q) 3 2 (meaning1628 q) (meaning1651 q) (meaning1662 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1906 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1651 = false ∨ valuation q 1662 = true := counterClause1906 (baseVal q)

theorem counterClause1907 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1682)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1674 q) 4 5 (meaning1598 q) (meaning1662 q) (meaning1682 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1907 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1662 = false ∨ valuation q 1682 = true := counterClause1907 (baseVal q)

theorem counterClause1908 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1682)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1674 q) 5 4 (meaning1599 q) (meaning1661 q) (meaning1682 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1908 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1661 = false ∨ valuation q 1682 = true := counterClause1908 (baseVal q)

theorem counterClause1909 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1683)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1674 q) 6 4 (meaning1600 q) (meaning1661 q) (meaning1683 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1909 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1661 = false ∨ valuation q 1683 = true := counterClause1909 (baseVal q)

theorem counterClause1910 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1697 = true := by
  have hs : count1697 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1697)) (countLit q [-63]) (countLit q [-66]) (count1697 q) 1 (meaningNeg63 q) (meaning1697 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1910 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1697 = true := counterClause1910 (baseVal q)

theorem counterClause1911 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1699)) (countLit q [-68]) (countLit q [-70]) (count1699 q) 1 (meaningNeg70 q) (meaning1699 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1911 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1699 = true := counterClause1911 (baseVal q)

theorem counterClause1912 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1699)) (countLit q [-68]) (countLit q [-70]) (count1699 q) 1 (meaningNeg68 q) (meaning1699 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1912 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1699 = true := counterClause1912 (baseVal q)

theorem counterClause1913 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1701 = true := by
  have hs : count1701 q = (countLit q [-63, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-68, -70])
  have hm := merge_right (literal (valuationOf q) (1699)) (literal (valuationOf q) (1701)) (countLit q [-63, -66]) (countLit q [-68, -70]) (count1701 q) 1 (meaning1699 q) (meaning1701 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1913 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1701 = true := counterClause1913 (baseVal q)

theorem counterClause1914 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1702 = true := by
  have hs : count1701 q = (countLit q [-63, -66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -66]) (l₂ := [-68, -70])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1702)) (countLit q [-63, -66]) (countLit q [-68, -70]) (count1701 q) 1 1 (meaning1697 q) (meaning1699 q) (meaning1702 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1914 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1699 = false ∨ valuation q 1702 = true := counterClause1914 (baseVal q)

theorem counterClause1915 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1705 = true := by
  have hs : count1705 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1705)) (countLit q [-71]) (countLit q [-74]) (count1705 q) 1 (meaningNeg74 q) (meaning1705 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1915 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1705 = true := counterClause1915 (baseVal q)

theorem counterClause1916 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1705 = true := by
  have hs : count1705 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1705)) (countLit q [-71]) (countLit q [-74]) (count1705 q) 1 (meaningNeg71 q) (meaning1705 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1916 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1705 = true := counterClause1916 (baseVal q)

theorem counterClause1917 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1707)) (countLit q [-76]) (countLit q [-78]) (count1707 q) 1 (meaningNeg78 q) (meaning1707 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1917 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1707 = true := counterClause1917 (baseVal q)

theorem counterClause1918 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1707)) (countLit q [-76]) (countLit q [-78]) (count1707 q) 1 (meaningNeg76 q) (meaning1707 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1918 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1707 = true := counterClause1918 (baseVal q)

theorem counterClause1919 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1710 = true := by
  have hs : count1709 q = (countLit q [-71, -74]) + (countLit q [-76, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-76, -78])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1710)) (countLit q [-71, -74]) (countLit q [-76, -78]) (count1709 q) 1 1 (meaning1705 q) (meaning1707 q) (meaning1710 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1919 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1707 = false ∨ valuation q 1710 = true := counterClause1919 (baseVal q)

theorem counterClause1920 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1715 = true := by
  have hs : count1713 q = (countLit q [-63, -66, -68, -70]) + (countLit q [-71, -74, -76, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -70]) (l₂ := [-71, -74, -76, -78])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1715)) (countLit q [-63, -66, -68, -70]) (countLit q [-71, -74, -76, -78]) (count1713 q) 1 2 (meaning1701 q) (meaning1710 q) (meaning1715 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1920 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1710 = false ∨ valuation q 1715 = true := counterClause1920 (baseVal q)

theorem block59 (q : Snake 81) (h : Conditions q) : B112E057.Block59 (valuation q) :=
  ⟨clause1889 q h, clause1890 q h, clause1891 q h, clause1892 q h, clause1893 q h, clause1894 q h, clause1895 q h, clause1896 q h, clause1897 q h, clause1898 q h, clause1899 q h, clause1900 q h, clause1901 q h, clause1902 q h, clause1903 q h, clause1904 q h, clause1905 q h, clause1906 q h, clause1907 q h, clause1908 q h, clause1909 q h, clause1910 q h, clause1911 q h, clause1912 q h, clause1913 q h, clause1914 q h, clause1915 q h, clause1916 q h, clause1917 q h, clause1918 q h, clause1919 q h, clause1920 q h⟩

end
end Snake9.Regrowth.E112057
