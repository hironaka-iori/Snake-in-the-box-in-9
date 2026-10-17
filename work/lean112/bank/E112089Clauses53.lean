import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1696 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1688)) (literal (valuationOf q) (1696)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 (meaning1688 q) (meaning1696 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1696 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1689)) (literal (valuationOf q) (1697)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 (meaning1689 q) (meaning1697 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1697 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1690)) (literal (valuationOf q) (1698)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 (meaning1690 q) (meaning1698 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1698 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1695)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 1 1 (meaning1663 q) (meaning1686 q) (meaning1695 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1686 = false ∨ valuation q 1695 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1696 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1696)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 1 2 (meaning1663 q) (meaning1687 q) (meaning1696 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1687 = false ∨ valuation q 1696 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 1 3 (meaning1663 q) (meaning1688 q) (meaning1697 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1688 = false ∨ valuation q 1697 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1698)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 1 4 (meaning1663 q) (meaning1689 q) (meaning1698 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1689 = false ∨ valuation q 1698 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1699)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 1 5 (meaning1663 q) (meaning1690 q) (meaning1699 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1690 = false ∨ valuation q 1699 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1700)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 1 6 (meaning1663 q) (meaning1691 q) (meaning1700 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1691 = false ∨ valuation q 1700 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1701)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 1 7 (meaning1663 q) (meaning1692 q) (meaning1701 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1692 = false ∨ valuation q 1701 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1696)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 2 1 (meaning1664 q) (meaning1686 q) (meaning1696 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1686 = false ∨ valuation q 1696 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1697)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 2 2 (meaning1664 q) (meaning1687 q) (meaning1697 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1687 = false ∨ valuation q 1697 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1698)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 2 3 (meaning1664 q) (meaning1688 q) (meaning1698 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1688 = false ∨ valuation q 1698 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1699)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 2 4 (meaning1664 q) (meaning1689 q) (meaning1699 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1689 = false ∨ valuation q 1699 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1700)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 2 5 (meaning1664 q) (meaning1690 q) (meaning1700 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1690 = false ∨ valuation q 1700 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1701)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 2 6 (meaning1664 q) (meaning1691 q) (meaning1701 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1691 = false ∨ valuation q 1701 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1702)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 2 7 (meaning1664 q) (meaning1692 q) (meaning1702 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1692 = false ∨ valuation q 1702 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1697)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 1 (meaning1665 q) (meaning1686 q) (meaning1697 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1686 = false ∨ valuation q 1697 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1698)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 2 (meaning1665 q) (meaning1687 q) (meaning1698 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1687 = false ∨ valuation q 1698 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1699)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 3 (meaning1665 q) (meaning1688 q) (meaning1699 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1688 = false ∨ valuation q 1699 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1700)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 4 (meaning1665 q) (meaning1689 q) (meaning1700 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1689 = false ∨ valuation q 1700 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1701)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 5 (meaning1665 q) (meaning1690 q) (meaning1701 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1690 = false ∨ valuation q 1701 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1702)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 6 (meaning1665 q) (meaning1691 q) (meaning1702 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1691 = false ∨ valuation q 1702 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1703)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 3 7 (meaning1665 q) (meaning1692 q) (meaning1703 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1692 = false ∨ valuation q 1703 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1698)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 1 (meaning1666 q) (meaning1686 q) (meaning1698 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1686 = false ∨ valuation q 1698 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1699)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 2 (meaning1666 q) (meaning1687 q) (meaning1699 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1687 = false ∨ valuation q 1699 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1700)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 3 (meaning1666 q) (meaning1688 q) (meaning1700 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1688 = false ∨ valuation q 1700 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1701)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 4 (meaning1666 q) (meaning1689 q) (meaning1701 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1689 = false ∨ valuation q 1701 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1702)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 5 (meaning1666 q) (meaning1690 q) (meaning1702 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1690 = false ∨ valuation q 1702 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1703)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 6 (meaning1666 q) (meaning1691 q) (meaning1703 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1691 = false ∨ valuation q 1703 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1704)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 4 7 (meaning1666 q) (meaning1692 q) (meaning1704 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1692 = false ∨ valuation q 1704 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1667)) (literal (valuationOf q) (1698)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 (meaning1667 q) (meaning1698 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1698 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E089.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112089
