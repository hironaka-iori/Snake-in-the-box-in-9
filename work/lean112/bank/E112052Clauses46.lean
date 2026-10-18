import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1676 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1676)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 2 (meaning1594 q) (meaning1656 q) (meaning1676 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1656 = false ∨ valuation q 1676 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1677)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 3 (meaning1594 q) (meaning1657 q) (meaning1677 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1657 = false ∨ valuation q 1677 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1678)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 4 (meaning1594 q) (meaning1658 q) (meaning1678 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1658 = false ∨ valuation q 1678 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1679)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 5 (meaning1594 q) (meaning1659 q) (meaning1679 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1659 = false ∨ valuation q 1679 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 6 (meaning1594 q) (meaning1660 q) (meaning1680 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1660 = false ∨ valuation q 1680 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1681)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 7 (meaning1594 q) (meaning1661 q) (meaning1681 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1661 = false ∨ valuation q 1681 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 8 (meaning1594 q) (meaning1662 q) (meaning1682 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1662 = false ∨ valuation q 1682 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 9 (meaning1594 q) (meaning1663 q) (meaning1683 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1663 = false ∨ valuation q 1683 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1676 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1676)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 1 (meaning1595 q) (meaning1655 q) (meaning1676 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1655 = false ∨ valuation q 1676 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1677)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 2 (meaning1595 q) (meaning1656 q) (meaning1677 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1656 = false ∨ valuation q 1677 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1678)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 3 (meaning1595 q) (meaning1657 q) (meaning1678 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1657 = false ∨ valuation q 1678 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1679)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 4 (meaning1595 q) (meaning1658 q) (meaning1679 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1658 = false ∨ valuation q 1679 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 5 (meaning1595 q) (meaning1659 q) (meaning1680 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1659 = false ∨ valuation q 1680 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1681)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 6 (meaning1595 q) (meaning1660 q) (meaning1681 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1660 = false ∨ valuation q 1681 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 7 (meaning1595 q) (meaning1661 q) (meaning1682 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1661 = false ∨ valuation q 1682 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 5 8 (meaning1595 q) (meaning1662 q) (meaning1683 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1662 = false ∨ valuation q 1683 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1677)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 6 1 (meaning1596 q) (meaning1655 q) (meaning1677 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1655 = false ∨ valuation q 1677 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1678)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 6 2 (meaning1596 q) (meaning1656 q) (meaning1678 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1656 = false ∨ valuation q 1678 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1679)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 6 3 (meaning1596 q) (meaning1657 q) (meaning1679 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1657 = false ∨ valuation q 1679 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 6 4 (meaning1596 q) (meaning1658 q) (meaning1680 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1658 = false ∨ valuation q 1680 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1681)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 6 5 (meaning1596 q) (meaning1659 q) (meaning1681 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1659 = false ∨ valuation q 1681 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 6 6 (meaning1596 q) (meaning1660 q) (meaning1682 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1660 = false ∨ valuation q 1682 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 6 7 (meaning1596 q) (meaning1661 q) (meaning1683 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1661 = false ∨ valuation q 1683 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1677)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 (meaning1597 q) (meaning1677 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1677 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1678)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 1 (meaning1597 q) (meaning1655 q) (meaning1678 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1655 = false ∨ valuation q 1678 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1679)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 2 (meaning1597 q) (meaning1656 q) (meaning1679 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1656 = false ∨ valuation q 1679 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 3 (meaning1597 q) (meaning1657 q) (meaning1680 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1657 = false ∨ valuation q 1680 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1681)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 4 (meaning1597 q) (meaning1658 q) (meaning1681 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1658 = false ∨ valuation q 1681 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1682)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 5 (meaning1597 q) (meaning1659 q) (meaning1682 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1659 = false ∨ valuation q 1682 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1683)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 6 (meaning1597 q) (meaning1660 q) (meaning1683 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1660 = false ∨ valuation q 1683 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1684 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1684)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 7 (meaning1597 q) (meaning1661 q) (meaning1684 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1661 = false ∨ valuation q 1684 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1685 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1685)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 7 8 (meaning1597 q) (meaning1662 q) (meaning1685 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1662 = false ∨ valuation q 1685 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E052.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112052
