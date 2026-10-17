import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1717 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1717)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 3 5 (meaning1681 q) (meaning1706 q) (meaning1717 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1706 = false ∨ valuation q 1717 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1718 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1718)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 3 6 (meaning1681 q) (meaning1707 q) (meaning1718 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1707 = false ∨ valuation q 1718 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1719 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1719)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 3 7 (meaning1681 q) (meaning1708 q) (meaning1719 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1708 = false ∨ valuation q 1719 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1714 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1714)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 1 (meaning1682 q) (meaning1702 q) (meaning1714 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1702 = false ∨ valuation q 1714 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1715 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1715)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 2 (meaning1682 q) (meaning1703 q) (meaning1715 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1703 = false ∨ valuation q 1715 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1716 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1716)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 3 (meaning1682 q) (meaning1704 q) (meaning1716 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1704 = false ∨ valuation q 1716 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1717 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1717)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 4 (meaning1682 q) (meaning1705 q) (meaning1717 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1705 = false ∨ valuation q 1717 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1718 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1718)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 5 (meaning1682 q) (meaning1706 q) (meaning1718 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1706 = false ∨ valuation q 1718 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1719 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1719)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 6 (meaning1682 q) (meaning1707 q) (meaning1719 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1707 = false ∨ valuation q 1719 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1720 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1720)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 4 7 (meaning1682 q) (meaning1708 q) (meaning1720 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1708 = false ∨ valuation q 1720 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1716 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1716)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 5 2 (meaning1683 q) (meaning1703 q) (meaning1716 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1703 = false ∨ valuation q 1716 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1717 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1717)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 5 3 (meaning1683 q) (meaning1704 q) (meaning1717 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1704 = false ∨ valuation q 1717 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1718 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1718)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 5 4 (meaning1683 q) (meaning1705 q) (meaning1718 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1705 = false ∨ valuation q 1718 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1719 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1719)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 5 5 (meaning1683 q) (meaning1706 q) (meaning1719 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1706 = false ∨ valuation q 1719 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1717 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1684)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1717)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 6 2 (meaning1684 q) (meaning1703 q) (meaning1717 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1703 = false ∨ valuation q 1717 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1718 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1684)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1718)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 6 3 (meaning1684 q) (meaning1704 q) (meaning1718 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1704 = false ∨ valuation q 1718 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1719 = true := by
  have hs : count1710 q = (countLit q [-91, -92, -95, -98, -99, -102, -103]) + (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -95, -98, -99, -102, -103]) (l₂ := [-107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1684)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1719)) (countLit q [-91, -92, -95, -98, -99, -102, -103]) (countLit q [-107, -110, -112, -113, -115, -116, -118, -120]) (count1710 q) 6 4 (meaning1684 q) (meaning1705 q) (meaning1719 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1705 = false ∨ valuation q 1719 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1733 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1733)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 1 8 (meaning1651 q) (meaning1717 q) (meaning1733 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1717 = false ∨ valuation q 1733 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1734 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1734)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 1 9 (meaning1651 q) (meaning1718 q) (meaning1734 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1718 = false ∨ valuation q 1734 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 1 10 (meaning1651 q) (meaning1719 q) (meaning1735 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1719 = false ∨ valuation q 1735 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1730 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1730)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 4 (meaning1652 q) (meaning1713 q) (meaning1730 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1713 = false ∨ valuation q 1730 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1731 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1731)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 5 (meaning1652 q) (meaning1714 q) (meaning1731 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1714 = false ∨ valuation q 1731 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1732 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1732)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 6 (meaning1652 q) (meaning1715 q) (meaning1732 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1715 = false ∨ valuation q 1732 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1733 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1733)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 7 (meaning1652 q) (meaning1716 q) (meaning1733 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1716 = false ∨ valuation q 1733 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1734 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1734)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 8 (meaning1652 q) (meaning1717 q) (meaning1734 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1717 = false ∨ valuation q 1734 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 9 (meaning1652 q) (meaning1718 q) (meaning1735 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1718 = false ∨ valuation q 1735 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 10 (meaning1652 q) (meaning1719 q) (meaning1736 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1719 = false ∨ valuation q 1736 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 2 11 (meaning1652 q) (meaning1720 q) (meaning1737 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1720 = false ∨ valuation q 1737 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1730 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1730)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 3 (meaning1653 q) (meaning1712 q) (meaning1730 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1712 = false ∨ valuation q 1730 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1731 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1731)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 4 (meaning1653 q) (meaning1713 q) (meaning1731 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1713 = false ∨ valuation q 1731 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1732 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1732)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 5 (meaning1653 q) (meaning1714 q) (meaning1732 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1714 = false ∨ valuation q 1732 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1733 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1733)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 3 6 (meaning1653 q) (meaning1715 q) (meaning1733 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1715 = false ∨ valuation q 1733 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E019.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112019
