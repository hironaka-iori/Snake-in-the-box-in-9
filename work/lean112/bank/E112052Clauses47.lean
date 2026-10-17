import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1678)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 (meaning1598 q) (meaning1678 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1678 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1679)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 1 (meaning1598 q) (meaning1655 q) (meaning1679 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1655 = false ∨ valuation q 1679 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 2 (meaning1598 q) (meaning1656 q) (meaning1680 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1656 = false ∨ valuation q 1680 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1681)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 3 (meaning1598 q) (meaning1657 q) (meaning1681 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1657 = false ∨ valuation q 1681 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 4 (meaning1598 q) (meaning1658 q) (meaning1682 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1658 = false ∨ valuation q 1682 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 5 (meaning1598 q) (meaning1659 q) (meaning1683 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1659 = false ∨ valuation q 1683 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1684 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1684)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 6 (meaning1598 q) (meaning1660 q) (meaning1684 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1660 = false ∨ valuation q 1684 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1685 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1685)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 7 (meaning1598 q) (meaning1661 q) (meaning1685 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1661 = false ∨ valuation q 1685 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1686 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1686)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 8 8 (meaning1598 q) (meaning1662 q) (meaning1686 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1662 = false ∨ valuation q 1686 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 9 1 (meaning1599 q) (meaning1655 q) (meaning1680 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1655 = false ∨ valuation q 1680 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1681)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 9 2 (meaning1599 q) (meaning1656 q) (meaning1681 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1656 = false ∨ valuation q 1681 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 9 3 (meaning1599 q) (meaning1657 q) (meaning1682 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1657 = false ∨ valuation q 1682 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 9 4 (meaning1599 q) (meaning1658 q) (meaning1683 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1658 = false ∨ valuation q 1683 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1684 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1684)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 9 5 (meaning1599 q) (meaning1659 q) (meaning1684 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1659 = false ∨ valuation q 1684 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1685 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1685)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 9 6 (meaning1599 q) (meaning1660 q) (meaning1685 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1660 = false ∨ valuation q 1685 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1686 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1686)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 9 7 (meaning1599 q) (meaning1661 q) (meaning1686 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1661 = false ∨ valuation q 1686 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 (meaning1600 q) (meaning1680 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1680 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1681)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 1 (meaning1600 q) (meaning1655 q) (meaning1681 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1655 = false ∨ valuation q 1681 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 2 (meaning1600 q) (meaning1656 q) (meaning1682 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1656 = false ∨ valuation q 1682 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 3 (meaning1600 q) (meaning1657 q) (meaning1683 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1657 = false ∨ valuation q 1683 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1684 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1684)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 4 (meaning1600 q) (meaning1658 q) (meaning1684 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1658 = false ∨ valuation q 1684 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1685 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1685)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 5 (meaning1600 q) (meaning1659 q) (meaning1685 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1659 = false ∨ valuation q 1685 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1686 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1686)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 6 (meaning1600 q) (meaning1660 q) (meaning1686 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1660 = false ∨ valuation q 1686 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1687 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1687)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 10 7 (meaning1600 q) (meaning1661 q) (meaning1687 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1661 = false ∨ valuation q 1687 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 11 1 (meaning1601 q) (meaning1655 q) (meaning1682 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1655 = false ∨ valuation q 1682 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 11 2 (meaning1601 q) (meaning1656 q) (meaning1683 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1656 = false ∨ valuation q 1683 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1685 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1685)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 11 4 (meaning1601 q) (meaning1658 q) (meaning1685 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1658 = false ∨ valuation q 1685 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1695 = true := by
  have hs : count1695 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1695)) (countLit q [-65]) (countLit q [-67]) (count1695 q) 1 (meaningNeg67 q) (meaning1695 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1695 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1695 = true := by
  have hs : count1695 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1695)) (countLit q [-65]) (countLit q [-67]) (count1695 q) 1 (meaningNeg65 q) (meaning1695 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1695 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1696)) (countLit q [-65]) (countLit q [-67]) (count1695 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning1696 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 1696 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1697 = true := by
  have hs : count1697 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1697)) (countLit q [-68]) (countLit q [-71]) (count1697 q) 1 (meaningNeg71 q) (meaning1697 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1697 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1697 = true := by
  have hs : count1697 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1697)) (countLit q [-68]) (countLit q [-71]) (count1697 q) 1 (meaningNeg68 q) (meaning1697 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1697 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E052.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112052
