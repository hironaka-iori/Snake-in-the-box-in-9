import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1696 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1696)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 9 (meaning1607 q) (meaning1674 q) (meaning1696 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1674 = false ∨ valuation q 1696 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1689 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1689)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 1 (meaning1608 q) (meaning1666 q) (meaning1689 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1666 = false ∨ valuation q 1689 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1690 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1690)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 2 (meaning1608 q) (meaning1667 q) (meaning1690 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1667 = false ∨ valuation q 1690 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1691 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1691)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 3 (meaning1608 q) (meaning1668 q) (meaning1691 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1668 = false ∨ valuation q 1691 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1692 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1692)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 4 (meaning1608 q) (meaning1669 q) (meaning1692 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1669 = false ∨ valuation q 1692 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1693 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1693)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 5 (meaning1608 q) (meaning1670 q) (meaning1693 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1670 = false ∨ valuation q 1693 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1694 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1694)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 6 (meaning1608 q) (meaning1671 q) (meaning1694 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1671 = false ∨ valuation q 1694 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1695 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1695)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 7 (meaning1608 q) (meaning1672 q) (meaning1695 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1672 = false ∨ valuation q 1695 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1696 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1696)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 7 8 (meaning1608 q) (meaning1673 q) (meaning1696 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1673 = false ∨ valuation q 1696 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1690 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1690)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 8 1 (meaning1609 q) (meaning1666 q) (meaning1690 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1666 = false ∨ valuation q 1690 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1691 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1691)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 8 2 (meaning1609 q) (meaning1667 q) (meaning1691 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1667 = false ∨ valuation q 1691 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1692 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1692)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 8 3 (meaning1609 q) (meaning1668 q) (meaning1692 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1668 = false ∨ valuation q 1692 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1693 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1693)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 8 4 (meaning1609 q) (meaning1669 q) (meaning1693 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1669 = false ∨ valuation q 1693 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1694 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1694)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 8 5 (meaning1609 q) (meaning1670 q) (meaning1694 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1670 = false ∨ valuation q 1694 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1695 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1695)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 8 6 (meaning1609 q) (meaning1671 q) (meaning1695 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1671 = false ∨ valuation q 1695 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1696 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1696)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 8 7 (meaning1609 q) (meaning1672 q) (meaning1696 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1672 = false ∨ valuation q 1696 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1691 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1691)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 9 1 (meaning1610 q) (meaning1666 q) (meaning1691 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1666 = false ∨ valuation q 1691 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1692 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1692)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 9 2 (meaning1610 q) (meaning1667 q) (meaning1692 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1667 = false ∨ valuation q 1692 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1693 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1693)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 9 3 (meaning1610 q) (meaning1668 q) (meaning1693 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1668 = false ∨ valuation q 1693 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1694 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1694)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 9 4 (meaning1610 q) (meaning1669 q) (meaning1694 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1669 = false ∨ valuation q 1694 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1695 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1695)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 9 5 (meaning1610 q) (meaning1670 q) (meaning1695 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1670 = false ∨ valuation q 1695 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1694 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1694)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 10 3 (meaning1611 q) (meaning1668 q) (meaning1694 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1668 = false ∨ valuation q 1694 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1696 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1696)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 10 5 (meaning1611 q) (meaning1670 q) (meaning1696 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1670 = false ∨ valuation q 1696 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1695 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1695)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 11 3 (meaning1612 q) (meaning1668 q) (meaning1695 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1668 = false ∨ valuation q 1695 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1707)) (countLit q [-65]) (countLit q [-66]) (count1707 q) 1 (meaningNeg66 q) (meaning1707 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1707 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1707)) (countLit q [-65]) (countLit q [-66]) (count1707 q) 1 (meaningNeg65 q) (meaning1707 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1707 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1708 = true := by
  have hs : count1707 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1708)) (countLit q [-65]) (countLit q [-66]) (count1707 q) 1 1 (meaningNeg65 q) (meaningNeg66 q) (meaning1708 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 1708 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1709)) (countLit q [-68]) (countLit q [-69]) (count1709 q) 1 (meaningNeg69 q) (meaning1709 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1709 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1709)) (countLit q [-68]) (countLit q [-69]) (count1709 q) 1 (meaningNeg68 q) (meaning1709 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1709 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1710 = true := by
  have hs : count1709 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1710)) (countLit q [-68]) (countLit q [-69]) (count1709 q) 1 1 (meaningNeg68 q) (meaningNeg69 q) (meaning1710 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 1710 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (1709)) (literal (valuationOf q) (1711)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 1 (meaning1709 q) (meaning1711 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1711 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (1710)) (literal (valuationOf q) (1712)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 2 (meaning1710 q) (meaning1712 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1712 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E050.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112050
