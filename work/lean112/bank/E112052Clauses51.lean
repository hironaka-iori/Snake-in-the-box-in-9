import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1742 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1742)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 4 4 (meaning1726 q) (meaning1734 q) (meaning1742 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1734 = false ∨ valuation q 1742 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1745 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1745)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 1 2 (meaning1711 q) (meaning1736 q) (meaning1745 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1736 = false ∨ valuation q 1745 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1746 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1746)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 1 3 (meaning1711 q) (meaning1737 q) (meaning1746 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1737 = false ∨ valuation q 1746 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1747 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1747)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 1 4 (meaning1711 q) (meaning1738 q) (meaning1747 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1738 = false ∨ valuation q 1747 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1748 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1748)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 1 5 (meaning1711 q) (meaning1739 q) (meaning1748 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1739 = false ∨ valuation q 1748 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1749 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1740)) (literal (valuationOf q) (1749)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 1 6 (meaning1711 q) (meaning1740 q) (meaning1749 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1740 = false ∨ valuation q 1749 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1750 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1750)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 1 7 (meaning1711 q) (meaning1741 q) (meaning1750 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1741 = false ∨ valuation q 1750 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1751 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1751)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 1 8 (meaning1711 q) (meaning1742 q) (meaning1751 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1742 = false ∨ valuation q 1751 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1745 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1745)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 1 (meaning1712 q) (meaning1735 q) (meaning1745 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1735 = false ∨ valuation q 1745 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1746 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1746)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 2 (meaning1712 q) (meaning1736 q) (meaning1746 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1736 = false ∨ valuation q 1746 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1747 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1747)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 3 (meaning1712 q) (meaning1737 q) (meaning1747 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1737 = false ∨ valuation q 1747 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1748 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1748)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 4 (meaning1712 q) (meaning1738 q) (meaning1748 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1738 = false ∨ valuation q 1748 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1749 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1749)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 5 (meaning1712 q) (meaning1739 q) (meaning1749 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1739 = false ∨ valuation q 1749 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1750 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1740)) (literal (valuationOf q) (1750)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 6 (meaning1712 q) (meaning1740 q) (meaning1750 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1740 = false ∨ valuation q 1750 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1751 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1751)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 7 (meaning1712 q) (meaning1741 q) (meaning1751 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1741 = false ∨ valuation q 1751 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1752 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1752)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 2 8 (meaning1712 q) (meaning1742 q) (meaning1752 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1742 = false ∨ valuation q 1752 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1746 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1746)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 1 (meaning1713 q) (meaning1735 q) (meaning1746 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1735 = false ∨ valuation q 1746 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1747 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1747)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 2 (meaning1713 q) (meaning1736 q) (meaning1747 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1736 = false ∨ valuation q 1747 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1748 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1748)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 3 (meaning1713 q) (meaning1737 q) (meaning1748 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1737 = false ∨ valuation q 1748 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1749 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1749)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 4 (meaning1713 q) (meaning1738 q) (meaning1749 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1738 = false ∨ valuation q 1749 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1750 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1750)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 5 (meaning1713 q) (meaning1739 q) (meaning1750 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1739 = false ∨ valuation q 1750 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1751 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1740)) (literal (valuationOf q) (1751)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 6 (meaning1713 q) (meaning1740 q) (meaning1751 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1740 = false ∨ valuation q 1751 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1752 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1752)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 7 (meaning1713 q) (meaning1741 q) (meaning1752 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1741 = false ∨ valuation q 1752 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1753 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1753)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 3 8 (meaning1713 q) (meaning1742 q) (meaning1753 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1742 = false ∨ valuation q 1753 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1747 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1747)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 1 (meaning1714 q) (meaning1735 q) (meaning1747 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1735 = false ∨ valuation q 1747 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1748 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1748)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 2 (meaning1714 q) (meaning1736 q) (meaning1748 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1736 = false ∨ valuation q 1748 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1749 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1749)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 3 (meaning1714 q) (meaning1737 q) (meaning1749 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1737 = false ∨ valuation q 1749 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1750 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1750)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 4 (meaning1714 q) (meaning1738 q) (meaning1750 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1738 = false ∨ valuation q 1750 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1751 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1751)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 5 (meaning1714 q) (meaning1739 q) (meaning1751 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1739 = false ∨ valuation q 1751 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1752 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1740)) (literal (valuationOf q) (1752)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 6 (meaning1714 q) (meaning1740 q) (meaning1752 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1740 = false ∨ valuation q 1752 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1753 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1753)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 7 (meaning1714 q) (meaning1741 q) (meaning1753 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1741 = false ∨ valuation q 1753 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1754 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1754)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 4 8 (meaning1714 q) (meaning1742 q) (meaning1754 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1742 = false ∨ valuation q 1754 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E052.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112052
