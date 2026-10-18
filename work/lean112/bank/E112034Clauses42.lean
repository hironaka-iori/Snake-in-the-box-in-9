import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1687 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1687)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 8 6 (meaning1595 q) (meaning1662 q) (meaning1687 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1662 = false ∨ valuation q 1687 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1688 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1688)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 8 7 (meaning1595 q) (meaning1663 q) (meaning1688 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1663 = false ∨ valuation q 1688 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1689 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1689)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 8 8 (meaning1595 q) (meaning1664 q) (meaning1689 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1664 = false ∨ valuation q 1689 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1690 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 8 9 (meaning1595 q) (meaning1665 q) (meaning1690 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1665 = false ∨ valuation q 1690 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1684 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1684)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 2 (meaning1596 q) (meaning1658 q) (meaning1684 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1658 = false ∨ valuation q 1684 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1685 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1685)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 3 (meaning1596 q) (meaning1659 q) (meaning1685 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1659 = false ∨ valuation q 1685 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1686 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1686)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 4 (meaning1596 q) (meaning1660 q) (meaning1686 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1660 = false ∨ valuation q 1686 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1687 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1687)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 5 (meaning1596 q) (meaning1661 q) (meaning1687 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1661 = false ∨ valuation q 1687 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1688 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1688)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 6 (meaning1596 q) (meaning1662 q) (meaning1688 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1662 = false ∨ valuation q 1688 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1689 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1689)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 7 (meaning1596 q) (meaning1663 q) (meaning1689 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1663 = false ∨ valuation q 1689 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1690 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 8 (meaning1596 q) (meaning1664 q) (meaning1690 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1664 = false ∨ valuation q 1690 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1691 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1691)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 9 9 (meaning1596 q) (meaning1665 q) (meaning1691 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1665 = false ∨ valuation q 1691 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1685 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1685)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 10 2 (meaning1597 q) (meaning1658 q) (meaning1685 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1658 = false ∨ valuation q 1685 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1686 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1686)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 10 3 (meaning1597 q) (meaning1659 q) (meaning1686 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1659 = false ∨ valuation q 1686 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1687 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1687)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 10 4 (meaning1597 q) (meaning1660 q) (meaning1687 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1660 = false ∨ valuation q 1687 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1688 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1688)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 10 5 (meaning1597 q) (meaning1661 q) (meaning1688 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1661 = false ∨ valuation q 1688 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1689 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1689)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 10 6 (meaning1597 q) (meaning1662 q) (meaning1689 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1662 = false ∨ valuation q 1689 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1690 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 10 7 (meaning1597 q) (meaning1663 q) (meaning1690 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1663 = false ∨ valuation q 1690 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1691 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1691)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 10 8 (meaning1597 q) (meaning1664 q) (meaning1691 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1664 = false ∨ valuation q 1691 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1687 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1687)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 11 3 (meaning1598 q) (meaning1659 q) (meaning1687 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1659 = false ∨ valuation q 1687 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1688 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1688)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 11 4 (meaning1598 q) (meaning1660 q) (meaning1688 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1660 = false ∨ valuation q 1688 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1689 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1689)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 11 5 (meaning1598 q) (meaning1661 q) (meaning1689 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1661 = false ∨ valuation q 1689 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1690 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 11 6 (meaning1598 q) (meaning1662 q) (meaning1690 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1662 = false ∨ valuation q 1690 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1691 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1691)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 11 7 (meaning1598 q) (meaning1663 q) (meaning1691 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1663 = false ∨ valuation q 1691 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1689 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1689)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 12 4 (meaning1599 q) (meaning1660 q) (meaning1689 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1660 = false ∨ valuation q 1689 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1690 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 13 4 (meaning1600 q) (meaning1660 q) (meaning1690 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1660 = false ∨ valuation q 1690 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1701 = true := by
  have hs : count1701 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1701)) (countLit q [-61]) (countLit q [-62]) (count1701 q) 1 (meaningNeg62 q) (meaning1701 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1701 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1701 = true := by
  have hs : count1701 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1701)) (countLit q [-61]) (countLit q [-62]) (count1701 q) 1 (meaningNeg61 q) (meaning1701 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1701 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1702 = true := by
  have hs : count1701 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1702)) (countLit q [-61]) (countLit q [-62]) (count1701 q) 1 1 (meaningNeg61 q) (meaningNeg62 q) (meaning1702 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 62 = true ∨ valuation q 1702 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1703 = true := by
  have hs : count1703 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1703)) (countLit q [-65]) (countLit q [-68]) (count1703 q) 1 (meaningNeg68 q) (meaning1703 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1703 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1703 = true := by
  have hs : count1703 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1703)) (countLit q [-65]) (countLit q [-68]) (count1703 q) 1 (meaningNeg65 q) (meaning1703 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1703 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1704 = true := by
  have hs : count1703 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1704)) (countLit q [-65]) (countLit q [-68]) (count1703 q) 1 1 (meaningNeg65 q) (meaningNeg68 q) (meaning1704 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 1704 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E034.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112034
