import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1702)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 6 3 (meaning1620 q) (meaning1680 q) (meaning1702 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1680 = false ∨ valuation q 1702 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1703)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 6 4 (meaning1620 q) (meaning1681 q) (meaning1703 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1681 = false ∨ valuation q 1703 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1704)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 6 5 (meaning1620 q) (meaning1682 q) (meaning1704 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1682 = false ∨ valuation q 1704 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1705)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 6 6 (meaning1620 q) (meaning1683 q) (meaning1705 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1683 = false ∨ valuation q 1705 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1706 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1706)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 6 7 (meaning1620 q) (meaning1684 q) (meaning1706 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1684 = false ∨ valuation q 1706 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1707 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1707)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 6 8 (meaning1620 q) (meaning1685 q) (meaning1707 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1685 = false ∨ valuation q 1707 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1703)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 7 3 (meaning1621 q) (meaning1680 q) (meaning1703 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1680 = false ∨ valuation q 1703 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1704)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 7 4 (meaning1621 q) (meaning1681 q) (meaning1704 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1681 = false ∨ valuation q 1704 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1705)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 7 5 (meaning1621 q) (meaning1682 q) (meaning1705 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1682 = false ∨ valuation q 1705 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1706 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1706)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 7 6 (meaning1621 q) (meaning1683 q) (meaning1706 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1683 = false ∨ valuation q 1706 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1705)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 8 4 (meaning1622 q) (meaning1681 q) (meaning1705 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1681 = false ∨ valuation q 1705 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1706 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1706)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 8 5 (meaning1622 q) (meaning1682 q) (meaning1706 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1682 = false ∨ valuation q 1706 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1707 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1707)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 8 6 (meaning1622 q) (meaning1683 q) (meaning1707 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1683 = false ∨ valuation q 1707 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1706 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1706)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 9 4 (meaning1623 q) (meaning1681 q) (meaning1706 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1681 = false ∨ valuation q 1706 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1707 = true := by
  have hs : count1694 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1707)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (count1694 q) 9 5 (meaning1623 q) (meaning1682 q) (meaning1707 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1682 = false ∨ valuation q 1707 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-64]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1717)) (countLit q [-64]) (countLit q [-67]) (count1717 q) 1 (meaningNeg64 q) (meaning1717 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1717 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1719)) (countLit q [-69]) (countLit q [-71]) (count1719 q) 1 (meaningNeg71 q) (meaning1719 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1719 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1719)) (countLit q [-69]) (countLit q [-71]) (count1719 q) 1 (meaningNeg69 q) (meaning1719 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1719 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1720)) (countLit q [-69]) (countLit q [-71]) (count1719 q) 1 1 (meaningNeg69 q) (meaningNeg71 q) (meaning1720 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 1720 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-64, -67]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -67]) (l₂ := [-69, -71])
  have hm := merge_right (literal (valuationOf q) (1719)) (literal (valuationOf q) (1721)) (countLit q [-64, -67]) (countLit q [-69, -71]) (count1721 q) 1 (meaning1719 q) (meaning1721 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1721 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-64, -67]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -67]) (l₂ := [-69, -71])
  have hm := merge_right (literal (valuationOf q) (1720)) (literal (valuationOf q) (1722)) (countLit q [-64, -67]) (countLit q [-69, -71]) (count1721 q) 2 (meaning1720 q) (meaning1722 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1722 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-64, -67]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -67]) (l₂ := [-69, -71])
  have hm := merge_left (literal (valuationOf q) (1717)) (literal (valuationOf q) (1721)) (countLit q [-64, -67]) (countLit q [-69, -71]) (count1721 q) 1 (meaning1717 q) (meaning1721 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1721 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-64, -67]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -67]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1722)) (countLit q [-64, -67]) (countLit q [-69, -71]) (count1721 q) 1 1 (meaning1717 q) (meaning1719 q) (meaning1722 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = false ∨ valuation q 1722 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1723 = true := by
  have hs : count1721 q = (countLit q [-64, -67]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -67]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1723)) (countLit q [-64, -67]) (countLit q [-69, -71]) (count1721 q) 1 2 (meaning1717 q) (meaning1720 q) (meaning1723 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1720 = false ∨ valuation q 1723 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-72]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1725)) (countLit q [-72]) (countLit q [-75]) (count1725 q) 1 (meaningNeg75 q) (meaning1725 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1725 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-72]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1725)) (countLit q [-72]) (countLit q [-75]) (count1725 q) 1 (meaningNeg72 q) (meaning1725 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1725 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 75 = true ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-72]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (1726)) (countLit q [-72]) (countLit q [-75]) (count1725 q) 1 1 (meaningNeg72 q) (meaningNeg75 q) (meaning1726 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 1726 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1727)) (countLit q [-77]) (countLit q [-79]) (count1727 q) 1 (meaningNeg79 q) (meaning1727 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1727 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1727)) (countLit q [-77]) (countLit q [-79]) (count1727 q) 1 (meaningNeg77 q) (meaning1727 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1727 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1728 = true := by
  have hs : count1727 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1728)) (countLit q [-77]) (countLit q [-79]) (count1727 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1728 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1728 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1729 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1727)) (literal (valuationOf q) (1729)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 1 (meaning1727 q) (meaning1729 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1729 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1728)) (literal (valuationOf q) (1730)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 2 (meaning1728 q) (meaning1730 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1730 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E055.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112055
