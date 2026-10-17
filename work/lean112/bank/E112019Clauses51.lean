import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1705 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1705)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 2 2 (meaning1691 q) (meaning1699 q) (meaning1705 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1699 = false ∨ valuation q 1705 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1706 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1706)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 2 3 (meaning1691 q) (meaning1700 q) (meaning1706 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1700 = false ∨ valuation q 1706 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1707 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1701)) (literal (valuationOf q) (1707)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 2 4 (meaning1691 q) (meaning1701 q) (meaning1707 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1701 = false ∨ valuation q 1707 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1704 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_left (literal (valuationOf q) (1692)) (literal (valuationOf q) (1704)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 3 (meaning1692 q) (meaning1704 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1704 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1705 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1705)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 3 1 (meaning1692 q) (meaning1698 q) (meaning1705 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1698 = false ∨ valuation q 1705 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1706 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1706)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 3 2 (meaning1692 q) (meaning1699 q) (meaning1706 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1699 = false ∨ valuation q 1706 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1707 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1707)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 3 3 (meaning1692 q) (meaning1700 q) (meaning1707 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1700 = false ∨ valuation q 1707 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1708 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1701)) (literal (valuationOf q) (1708)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 3 4 (meaning1692 q) (meaning1701 q) (meaning1708 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1701 = false ∨ valuation q 1708 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1705 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_left (literal (valuationOf q) (1693)) (literal (valuationOf q) (1705)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 4 (meaning1693 q) (meaning1705 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1705 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1706 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1706)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 4 1 (meaning1693 q) (meaning1698 q) (meaning1706 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1698 = false ∨ valuation q 1706 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1707 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1707)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 4 2 (meaning1693 q) (meaning1699 q) (meaning1707 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1699 = false ∨ valuation q 1707 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1708 = true := by
  have hs : count1702 q = (countLit q [-107, -110, -112, -113]) + (countLit q [-115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -113]) (l₂ := [-115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1708)) (countLit q [-107, -110, -112, -113]) (countLit q [-115, -116, -118, -120]) (count1702 q) 4 3 (meaning1693 q) (meaning1700 q) (meaning1708 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1700 = false ∨ valuation q 1708 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1713 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_right (literal (valuationOf q) (1705)) (literal (valuationOf q) (1713)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 (meaning1705 q) (meaning1713 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1713 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1714 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_right (literal (valuationOf q) (1706)) (literal (valuationOf q) (1714)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 5 (meaning1706 q) (meaning1714 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1714 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1715 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_right (literal (valuationOf q) (1707)) (literal (valuationOf q) (1715)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 6 (meaning1707 q) (meaning1715 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1715 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1712 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1712)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 1 2 (meaning1679 q) (meaning1703 q) (meaning1712 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1703 = false ∨ valuation q 1712 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1713 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1713)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 1 3 (meaning1679 q) (meaning1704 q) (meaning1713 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1704 = false ∨ valuation q 1713 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1714 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1714)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 1 4 (meaning1679 q) (meaning1705 q) (meaning1714 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1705 = false ∨ valuation q 1714 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1715 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1715)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 1 5 (meaning1679 q) (meaning1706 q) (meaning1715 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1706 = false ∨ valuation q 1715 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1716 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1716)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 1 6 (meaning1679 q) (meaning1707 q) (meaning1716 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1707 = false ∨ valuation q 1716 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1717 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1717)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 1 7 (meaning1679 q) (meaning1708 q) (meaning1717 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1708 = false ∨ valuation q 1717 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1712 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1712)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 2 1 (meaning1680 q) (meaning1702 q) (meaning1712 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1702 = false ∨ valuation q 1712 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1713 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1713)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 2 2 (meaning1680 q) (meaning1703 q) (meaning1713 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1703 = false ∨ valuation q 1713 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1714 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1714)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 2 3 (meaning1680 q) (meaning1704 q) (meaning1714 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1704 = false ∨ valuation q 1714 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1715 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1715)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 2 4 (meaning1680 q) (meaning1705 q) (meaning1715 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1705 = false ∨ valuation q 1715 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1716 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1716)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 2 5 (meaning1680 q) (meaning1706 q) (meaning1716 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1706 = false ∨ valuation q 1716 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1717 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1717)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 2 6 (meaning1680 q) (meaning1707 q) (meaning1717 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1707 = false ∨ valuation q 1717 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1718 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1718)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 2 7 (meaning1680 q) (meaning1708 q) (meaning1718 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1708 = false ∨ valuation q 1718 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1713 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1713)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 3 1 (meaning1681 q) (meaning1702 q) (meaning1713 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1702 = false ∨ valuation q 1713 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1714 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1714)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 3 2 (meaning1681 q) (meaning1703 q) (meaning1714 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1703 = false ∨ valuation q 1714 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1715 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1715)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 3 3 (meaning1681 q) (meaning1704 q) (meaning1715 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1704 = false ∨ valuation q 1715 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1716 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1716)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 3 4 (meaning1681 q) (meaning1705 q) (meaning1716 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1705 = false ∨ valuation q 1716 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E019.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112019
