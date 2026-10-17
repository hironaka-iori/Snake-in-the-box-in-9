import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1691 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1679)) (literal (valuationOf q) (1691)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 4 (meaning1679 q) (meaning1691 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1691 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1692 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1692)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 4 1 (meaning1679 q) (meaning1684 q) (meaning1692 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1684 = false ∨ valuation q 1692 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1693 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1693)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 4 2 (meaning1679 q) (meaning1685 q) (meaning1693 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1685 = false ∨ valuation q 1693 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1694 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1694)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 4 3 (meaning1679 q) (meaning1686 q) (meaning1694 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1686 = false ∨ valuation q 1694 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1696 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1688)) (literal (valuationOf q) (1696)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 (meaning1688 q) (meaning1696 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1696 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1697 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1689)) (literal (valuationOf q) (1697)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 (meaning1689 q) (meaning1697 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1697 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1698 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1690)) (literal (valuationOf q) (1698)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 3 (meaning1690 q) (meaning1698 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1698 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1699 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1691)) (literal (valuationOf q) (1699)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 4 (meaning1691 q) (meaning1699 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1699 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1700 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1692)) (literal (valuationOf q) (1700)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 5 (meaning1692 q) (meaning1700 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1700 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1701 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1693)) (literal (valuationOf q) (1701)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 6 (meaning1693 q) (meaning1701 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1701 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1696 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1665)) (literal (valuationOf q) (1696)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 (meaning1665 q) (meaning1696 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1696 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 1 (meaning1665 q) (meaning1688 q) (meaning1697 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1688 = false ∨ valuation q 1697 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1698)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 2 (meaning1665 q) (meaning1689 q) (meaning1698 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1689 = false ∨ valuation q 1698 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1699 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1699)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 3 (meaning1665 q) (meaning1690 q) (meaning1699 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1690 = false ∨ valuation q 1699 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1700 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1700)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 4 (meaning1665 q) (meaning1691 q) (meaning1700 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1691 = false ∨ valuation q 1700 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1701 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1701)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 5 (meaning1665 q) (meaning1692 q) (meaning1701 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1692 = false ∨ valuation q 1701 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1702 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1702)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 6 (meaning1665 q) (meaning1693 q) (meaning1702 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1693 = false ∨ valuation q 1702 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1703 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1703)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 1 7 (meaning1665 q) (meaning1694 q) (meaning1703 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1694 = false ∨ valuation q 1703 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1697 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1666)) (literal (valuationOf q) (1697)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 (meaning1666 q) (meaning1697 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1697 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1698)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 1 (meaning1666 q) (meaning1688 q) (meaning1698 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1688 = false ∨ valuation q 1698 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1699)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 2 (meaning1666 q) (meaning1689 q) (meaning1699 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1689 = false ∨ valuation q 1699 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1700)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 3 (meaning1666 q) (meaning1690 q) (meaning1700 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1690 = false ∨ valuation q 1700 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1701 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1701)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 4 (meaning1666 q) (meaning1691 q) (meaning1701 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1691 = false ∨ valuation q 1701 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1702 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1702)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 5 (meaning1666 q) (meaning1692 q) (meaning1702 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1692 = false ∨ valuation q 1702 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1703 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1703)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 2 6 (meaning1666 q) (meaning1693 q) (meaning1703 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1693 = false ∨ valuation q 1703 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1698 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1667)) (literal (valuationOf q) (1698)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 3 (meaning1667 q) (meaning1698 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1698 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1699)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 3 1 (meaning1667 q) (meaning1688 q) (meaning1699 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1688 = false ∨ valuation q 1699 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1700)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 3 2 (meaning1667 q) (meaning1689 q) (meaning1700 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1689 = false ∨ valuation q 1700 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1701)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 3 3 (meaning1667 q) (meaning1690 q) (meaning1701 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1690 = false ∨ valuation q 1701 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1702 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1702)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 3 4 (meaning1667 q) (meaning1691 q) (meaning1702 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1691 = false ∨ valuation q 1702 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1703 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1703)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 3 5 (meaning1667 q) (meaning1692 q) (meaning1703 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1692 = false ∨ valuation q 1703 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1699 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1668)) (literal (valuationOf q) (1699)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 4 (meaning1668 q) (meaning1699 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1699 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E105.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112105
