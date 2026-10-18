import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1685 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1685)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 4 4 (meaning1649 q) (meaning1673 q) (meaning1685 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1673 = false ∨ valuation q 1685 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1682 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1650)) (literal (valuationOf q) (1682)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 5 (meaning1650 q) (meaning1682 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1682 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1683 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1683)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 5 1 (meaning1650 q) (meaning1670 q) (meaning1683 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1670 = false ∨ valuation q 1683 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1684 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1684)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 5 2 (meaning1650 q) (meaning1671 q) (meaning1684 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1671 = false ∨ valuation q 1684 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1685 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1685)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 5 3 (meaning1650 q) (meaning1672 q) (meaning1685 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1672 = false ∨ valuation q 1685 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1686 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1686)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 5 4 (meaning1650 q) (meaning1673 q) (meaning1686 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1673 = false ∨ valuation q 1686 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1683 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1651)) (literal (valuationOf q) (1683)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 6 (meaning1651 q) (meaning1683 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1683 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1684 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1684)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 6 1 (meaning1651 q) (meaning1670 q) (meaning1684 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1670 = false ∨ valuation q 1684 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1685 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1685)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 6 2 (meaning1651 q) (meaning1671 q) (meaning1685 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1671 = false ∨ valuation q 1685 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1687 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1687)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 6 4 (meaning1651 q) (meaning1673 q) (meaning1687 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1673 = false ∨ valuation q 1687 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1700)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 2 5 (meaning1616 q) (meaning1682 q) (meaning1700 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1682 = false ∨ valuation q 1700 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1703)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 2 8 (meaning1616 q) (meaning1685 q) (meaning1703 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1685 = false ∨ valuation q 1703 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1700)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 3 4 (meaning1617 q) (meaning1681 q) (meaning1700 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1681 = false ∨ valuation q 1700 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1701)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 3 5 (meaning1617 q) (meaning1682 q) (meaning1701 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1682 = false ∨ valuation q 1701 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1702)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 3 6 (meaning1617 q) (meaning1683 q) (meaning1702 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1683 = false ∨ valuation q 1702 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1703)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 3 7 (meaning1617 q) (meaning1684 q) (meaning1703 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1684 = false ∨ valuation q 1703 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1704)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 3 8 (meaning1617 q) (meaning1685 q) (meaning1704 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1685 = false ∨ valuation q 1704 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1705)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 3 9 (meaning1617 q) (meaning1686 q) (meaning1705 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1686 = false ∨ valuation q 1705 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1700)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 4 3 (meaning1618 q) (meaning1680 q) (meaning1700 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1680 = false ∨ valuation q 1700 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1701)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 4 4 (meaning1618 q) (meaning1681 q) (meaning1701 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1681 = false ∨ valuation q 1701 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1702)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 4 5 (meaning1618 q) (meaning1682 q) (meaning1702 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1682 = false ∨ valuation q 1702 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1703)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 4 6 (meaning1618 q) (meaning1683 q) (meaning1703 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1683 = false ∨ valuation q 1703 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1704)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 4 7 (meaning1618 q) (meaning1684 q) (meaning1704 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1684 = false ∨ valuation q 1704 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1705)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 4 8 (meaning1618 q) (meaning1685 q) (meaning1705 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1685 = false ∨ valuation q 1705 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1707 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1707)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 4 10 (meaning1618 q) (meaning1687 q) (meaning1707 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1687 = false ∨ valuation q 1707 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1701)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 5 3 (meaning1619 q) (meaning1680 q) (meaning1701 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1680 = false ∨ valuation q 1701 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1702)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 5 4 (meaning1619 q) (meaning1681 q) (meaning1702 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1681 = false ∨ valuation q 1702 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1703)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 5 5 (meaning1619 q) (meaning1682 q) (meaning1703 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1682 = false ∨ valuation q 1703 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1704)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 5 6 (meaning1619 q) (meaning1683 q) (meaning1704 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1683 = false ∨ valuation q 1704 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1705)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 5 7 (meaning1619 q) (meaning1684 q) (meaning1705 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1684 = false ∨ valuation q 1705 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1706 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1706)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 5 8 (meaning1619 q) (meaning1685 q) (meaning1706 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1685 = false ∨ valuation q 1706 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1707 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1707)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 5 9 (meaning1619 q) (meaning1686 q) (meaning1707 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1686 = false ∨ valuation q 1707 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E055.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112055
