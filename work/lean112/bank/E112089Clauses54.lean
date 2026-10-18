import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1699)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 1 (meaning1667 q) (meaning1686 q) (meaning1699 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1686 = false ∨ valuation q 1699 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1700)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 2 (meaning1667 q) (meaning1687 q) (meaning1700 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1687 = false ∨ valuation q 1700 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1701)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 3 (meaning1667 q) (meaning1688 q) (meaning1701 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1688 = false ∨ valuation q 1701 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1702)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 4 (meaning1667 q) (meaning1689 q) (meaning1702 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1689 = false ∨ valuation q 1702 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1703)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 5 (meaning1667 q) (meaning1690 q) (meaning1703 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1690 = false ∨ valuation q 1703 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1704)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 6 (meaning1667 q) (meaning1691 q) (meaning1704 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1691 = false ∨ valuation q 1704 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1705)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 5 7 (meaning1667 q) (meaning1692 q) (meaning1705 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1692 = false ∨ valuation q 1705 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1668)) (literal (valuationOf q) (1699)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 (meaning1668 q) (meaning1699 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1699 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1700)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 1 (meaning1668 q) (meaning1686 q) (meaning1700 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1686 = false ∨ valuation q 1700 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1701)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 2 (meaning1668 q) (meaning1687 q) (meaning1701 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1687 = false ∨ valuation q 1701 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1702)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 3 (meaning1668 q) (meaning1688 q) (meaning1702 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1688 = false ∨ valuation q 1702 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1703)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 4 (meaning1668 q) (meaning1689 q) (meaning1703 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1689 = false ∨ valuation q 1703 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1704)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 5 (meaning1668 q) (meaning1690 q) (meaning1704 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1690 = false ∨ valuation q 1704 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1705 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1705)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 6 (meaning1668 q) (meaning1691 q) (meaning1705 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1691 = false ∨ valuation q 1705 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1706 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1706)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 6 7 (meaning1668 q) (meaning1692 q) (meaning1706 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1692 = false ∨ valuation q 1706 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1701)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 7 1 (meaning1669 q) (meaning1686 q) (meaning1701 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1686 = false ∨ valuation q 1701 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1702)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 7 2 (meaning1669 q) (meaning1687 q) (meaning1702 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1687 = false ∨ valuation q 1702 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1703 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1703)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 7 3 (meaning1669 q) (meaning1688 q) (meaning1703 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1688 = false ∨ valuation q 1703 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1704 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1704)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 7 4 (meaning1669 q) (meaning1689 q) (meaning1704 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1689 = false ∨ valuation q 1704 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1706 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1706)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 7 6 (meaning1669 q) (meaning1691 q) (meaning1706 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1691 = false ∨ valuation q 1706 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1707 = true := by
  have hs : count1694 q = (countLit q [-62, -64, -66, -67, -69, -72, -73]) + (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73]) (l₂ := [-75, -76, -79, -81, -85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1692)) (literal (valuationOf q) (1707)) (countLit q [-62, -64, -66, -67, -69, -72, -73]) (countLit q [-75, -76, -79, -81, -85, -87, -89, -91]) (count1694 q) 7 7 (meaning1669 q) (meaning1692 q) (meaning1707 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1692 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1692 = false ∨ valuation q 1707 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1709)) (countLit q [-94]) (countLit q [-96]) (count1709 q) 1 (meaningNeg96 q) (meaning1709 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1709 = true := counterClause1750 (baseVal q)

theorem counterClause1751 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1709)) (countLit q [-94]) (countLit q [-96]) (count1709 q) 1 (meaningNeg94 q) (meaning1709 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1709 = true := counterClause1751 (baseVal q)

theorem counterClause1752 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1710 = true := by
  have hs : count1709 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1710)) (countLit q [-94]) (countLit q [-96]) (count1709 q) 1 1 (meaningNeg94 q) (meaningNeg96 q) (meaning1710 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 1710 = true := counterClause1752 (baseVal q)

theorem counterClause1753 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1711)) (countLit q [-98]) (countLit q [-99]) (count1711 q) 1 (meaningNeg99 q) (meaning1711 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1711 = true := counterClause1753 (baseVal q)

theorem counterClause1754 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1711)) (countLit q [-98]) (countLit q [-99]) (count1711 q) 1 (meaningNeg98 q) (meaning1711 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1711 = true := counterClause1754 (baseVal q)

theorem counterClause1755 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1712)) (countLit q [-98]) (countLit q [-99]) (count1711 q) 1 1 (meaningNeg98 q) (meaningNeg99 q) (meaning1712 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 1712 = true := counterClause1755 (baseVal q)

theorem counterClause1756 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1713 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_right (literal (valuationOf q) (1711)) (literal (valuationOf q) (1713)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 1 (meaning1711 q) (meaning1713 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1713 = true := counterClause1756 (baseVal q)

theorem counterClause1757 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_right (literal (valuationOf q) (1712)) (literal (valuationOf q) (1714)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 2 (meaning1712 q) (meaning1714 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1714 = true := counterClause1757 (baseVal q)

theorem counterClause1758 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1713 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_left (literal (valuationOf q) (1709)) (literal (valuationOf q) (1713)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 1 (meaning1709 q) (meaning1713 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1713 = true := counterClause1758 (baseVal q)

theorem counterClause1759 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1711)) (literal (valuationOf q) (1714)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 1 1 (meaning1709 q) (meaning1711 q) (meaning1714 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1711 = false ∨ valuation q 1714 = true := counterClause1759 (baseVal q)

theorem counterClause1760 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1715 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1715)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 1 2 (meaning1709 q) (meaning1712 q) (meaning1715 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1712 = false ∨ valuation q 1715 = true := counterClause1760 (baseVal q)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E089.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112089
