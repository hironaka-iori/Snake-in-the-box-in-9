import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1693)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 2 5 (meaning1656 q) (meaning1683 q) (meaning1693 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1683 = false ∨ valuation q 1693 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1694)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 2 6 (meaning1656 q) (meaning1684 q) (meaning1694 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1684 = false ∨ valuation q 1694 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1690 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1690)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 3 1 (meaning1657 q) (meaning1679 q) (meaning1690 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1679 = false ∨ valuation q 1690 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1691 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1691)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 3 2 (meaning1657 q) (meaning1680 q) (meaning1691 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1680 = false ∨ valuation q 1691 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1692)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 3 3 (meaning1657 q) (meaning1681 q) (meaning1692 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1681 = false ∨ valuation q 1692 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1693)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 3 4 (meaning1657 q) (meaning1682 q) (meaning1693 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1682 = false ∨ valuation q 1693 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1694)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 3 5 (meaning1657 q) (meaning1683 q) (meaning1694 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1683 = false ∨ valuation q 1694 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1691 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1691)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 4 1 (meaning1658 q) (meaning1679 q) (meaning1691 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1679 = false ∨ valuation q 1691 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1692)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 4 2 (meaning1658 q) (meaning1680 q) (meaning1692 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1680 = false ∨ valuation q 1692 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1693)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 4 3 (meaning1658 q) (meaning1681 q) (meaning1693 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1681 = false ∨ valuation q 1693 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1694)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 4 4 (meaning1658 q) (meaning1682 q) (meaning1694 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1682 = false ∨ valuation q 1694 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1695 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1695)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 4 5 (meaning1658 q) (meaning1683 q) (meaning1695 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1683 = false ∨ valuation q 1695 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1692)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 5 1 (meaning1659 q) (meaning1679 q) (meaning1692 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1679 = false ∨ valuation q 1692 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1693)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 5 2 (meaning1659 q) (meaning1680 q) (meaning1693 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1680 = false ∨ valuation q 1693 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1694)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 5 3 (meaning1659 q) (meaning1681 q) (meaning1694 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1681 = false ∨ valuation q 1694 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1695 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1695)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 5 4 (meaning1659 q) (meaning1682 q) (meaning1695 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1682 = false ∨ valuation q 1695 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1693 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1693)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 6 1 (meaning1660 q) (meaning1679 q) (meaning1693 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1679 = false ∨ valuation q 1693 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1694 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1694)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 6 2 (meaning1660 q) (meaning1680 q) (meaning1694 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1680 = false ∨ valuation q 1694 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1695 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1695)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 6 3 (meaning1660 q) (meaning1681 q) (meaning1695 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1681 = false ∨ valuation q 1695 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1707 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1691)) (literal (valuationOf q) (1707)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 5 (meaning1691 q) (meaning1707 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1707 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1708 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1692)) (literal (valuationOf q) (1708)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 6 (meaning1692 q) (meaning1708 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1708 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1709 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1693)) (literal (valuationOf q) (1709)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 7 (meaning1693 q) (meaning1709 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1709 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1708 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1708)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 1 5 (meaning1624 q) (meaning1691 q) (meaning1708 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1691 = false ∨ valuation q 1708 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1709 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1709)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 1 6 (meaning1624 q) (meaning1692 q) (meaning1709 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1692 = false ∨ valuation q 1709 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 1 7 (meaning1624 q) (meaning1693 q) (meaning1710 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1693 = false ∨ valuation q 1710 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1708 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1708)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 2 4 (meaning1625 q) (meaning1690 q) (meaning1708 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1690 = false ∨ valuation q 1708 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1709 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1709)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 2 5 (meaning1625 q) (meaning1691 q) (meaning1709 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1691 = false ∨ valuation q 1709 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1710 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1710)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 2 6 (meaning1625 q) (meaning1692 q) (meaning1710 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1692 = false ∨ valuation q 1710 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1711 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1711)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 2 7 (meaning1625 q) (meaning1693 q) (meaning1711 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1693 = false ∨ valuation q 1711 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1712 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1712)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 2 8 (meaning1625 q) (meaning1694 q) (meaning1712 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1694 = false ∨ valuation q 1712 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1713 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1713)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 2 9 (meaning1625 q) (meaning1695 q) (meaning1713 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1695 = false ∨ valuation q 1713 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1709 = true := by
  have hs : count1703 q = (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) + (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (l₂ := [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1709)) (countLit q [-61, -62, -64, -67, -70, -71, -73, -75, -78, -80, -82, -83, -84, -86, -87]) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105, -106, -108, -109, -111, -114, -116, -117, -119]) (count1703 q) 3 4 (meaning1626 q) (meaning1690 q) (meaning1709 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1690 = false ∨ valuation q 1709 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E004.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112004
