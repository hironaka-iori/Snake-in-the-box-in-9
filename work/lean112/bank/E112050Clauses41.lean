import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1674 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1674)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 5 4 (meaning1638 q) (meaning1661 q) (meaning1674 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1661 = false ∨ valuation q 1674 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1675 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1675)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 5 5 (meaning1638 q) (meaning1662 q) (meaning1675 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1662 = false ∨ valuation q 1675 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1673 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1673)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 6 2 (meaning1639 q) (meaning1659 q) (meaning1673 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1659 = false ∨ valuation q 1673 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1689 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1689)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 3 5 (meaning1604 q) (meaning1670 q) (meaning1689 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1670 = false ∨ valuation q 1689 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1686)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 1 (meaning1605 q) (meaning1666 q) (meaning1686 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1666 = false ∨ valuation q 1686 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1687 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1687)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 2 (meaning1605 q) (meaning1667 q) (meaning1687 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1667 = false ∨ valuation q 1687 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1688 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1688)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 3 (meaning1605 q) (meaning1668 q) (meaning1688 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1668 = false ∨ valuation q 1688 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1689 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1689)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 4 (meaning1605 q) (meaning1669 q) (meaning1689 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1669 = false ∨ valuation q 1689 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1690 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1690)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 5 (meaning1605 q) (meaning1670 q) (meaning1690 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1670 = false ∨ valuation q 1690 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1691 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1691)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 6 (meaning1605 q) (meaning1671 q) (meaning1691 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1671 = false ∨ valuation q 1691 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1692 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1692)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 7 (meaning1605 q) (meaning1672 q) (meaning1692 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1672 = false ∨ valuation q 1692 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1693 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1693)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 8 (meaning1605 q) (meaning1673 q) (meaning1693 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1673 = false ∨ valuation q 1693 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1694 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1694)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 9 (meaning1605 q) (meaning1674 q) (meaning1694 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1674 = false ∨ valuation q 1694 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1695 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1695)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 4 10 (meaning1605 q) (meaning1675 q) (meaning1695 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1675 = false ∨ valuation q 1695 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1687)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 1 (meaning1606 q) (meaning1666 q) (meaning1687 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1666 = false ∨ valuation q 1687 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1688 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1688)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 2 (meaning1606 q) (meaning1667 q) (meaning1688 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1667 = false ∨ valuation q 1688 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1689 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1689)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 3 (meaning1606 q) (meaning1668 q) (meaning1689 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1668 = false ∨ valuation q 1689 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1690 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1690)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 4 (meaning1606 q) (meaning1669 q) (meaning1690 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1669 = false ∨ valuation q 1690 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1691 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1691)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 5 (meaning1606 q) (meaning1670 q) (meaning1691 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1670 = false ∨ valuation q 1691 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1692 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1692)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 6 (meaning1606 q) (meaning1671 q) (meaning1692 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1671 = false ∨ valuation q 1692 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1693 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1693)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 7 (meaning1606 q) (meaning1672 q) (meaning1693 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1672 = false ∨ valuation q 1693 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1694 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1694)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 8 (meaning1606 q) (meaning1673 q) (meaning1694 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1673 = false ∨ valuation q 1694 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1695 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1695)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 9 (meaning1606 q) (meaning1674 q) (meaning1695 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1674 = false ∨ valuation q 1695 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1696 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1696)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 5 10 (meaning1606 q) (meaning1675 q) (meaning1696 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1675 = false ∨ valuation q 1696 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1688 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1688)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 1 (meaning1607 q) (meaning1666 q) (meaning1688 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1666 = false ∨ valuation q 1688 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1689 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1689)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 2 (meaning1607 q) (meaning1667 q) (meaning1689 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1667 = false ∨ valuation q 1689 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1690 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1690)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 3 (meaning1607 q) (meaning1668 q) (meaning1690 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1668 = false ∨ valuation q 1690 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1691 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1691)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 4 (meaning1607 q) (meaning1669 q) (meaning1691 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1669 = false ∨ valuation q 1691 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1692 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1692)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 5 (meaning1607 q) (meaning1670 q) (meaning1692 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1670 = false ∨ valuation q 1692 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1693 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1693)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 6 (meaning1607 q) (meaning1671 q) (meaning1693 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1671 = false ∨ valuation q 1693 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1694 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1694)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 7 (meaning1607 q) (meaning1672 q) (meaning1694 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1672 = false ∨ valuation q 1694 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1695 = true := by
  have hs : count1682 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1695)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -13, -16, -18, -19, -21, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1682 q) 6 8 (meaning1607 q) (meaning1673 q) (meaning1695 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1673 = false ∨ valuation q 1695 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E050.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112050
