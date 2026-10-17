import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1747 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1747)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 (meaning1715 q) (meaning1747 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1747 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1748 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1748)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 1 (meaning1715 q) (meaning1735 q) (meaning1748 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1735 = false ∨ valuation q 1748 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1749 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1749)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 2 (meaning1715 q) (meaning1736 q) (meaning1749 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1736 = false ∨ valuation q 1749 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1750 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1750)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 3 (meaning1715 q) (meaning1737 q) (meaning1750 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1737 = false ∨ valuation q 1750 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1751 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1751)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 4 (meaning1715 q) (meaning1738 q) (meaning1751 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1738 = false ∨ valuation q 1751 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1752 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1752)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 5 (meaning1715 q) (meaning1739 q) (meaning1752 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1739 = false ∨ valuation q 1752 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1753 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1740)) (literal (valuationOf q) (1753)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 6 (meaning1715 q) (meaning1740 q) (meaning1753 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1740 = false ∨ valuation q 1753 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1754 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1754)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 7 (meaning1715 q) (meaning1741 q) (meaning1754 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1741 = false ∨ valuation q 1754 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1755 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1755)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 5 8 (meaning1715 q) (meaning1742 q) (meaning1755 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1742 = false ∨ valuation q 1755 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1751 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1751)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 6 3 (meaning1716 q) (meaning1737 q) (meaning1751 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1737 = false ∨ valuation q 1751 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1752 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1752)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 6 4 (meaning1716 q) (meaning1738 q) (meaning1752 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1738 = false ∨ valuation q 1752 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1753 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1753)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 6 5 (meaning1716 q) (meaning1739 q) (meaning1753 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1739 = false ∨ valuation q 1753 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1754 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1740)) (literal (valuationOf q) (1754)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 6 6 (meaning1716 q) (meaning1740 q) (meaning1754 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1740 = false ∨ valuation q 1754 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1755 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1755)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 6 7 (meaning1716 q) (meaning1741 q) (meaning1755 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1741 = false ∨ valuation q 1755 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1750 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1750)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 7 1 (meaning1717 q) (meaning1735 q) (meaning1750 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1735 = false ∨ valuation q 1750 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1751 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1751)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 7 2 (meaning1717 q) (meaning1736 q) (meaning1751 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1736 = false ∨ valuation q 1751 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1752 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1752)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 7 3 (meaning1717 q) (meaning1737 q) (meaning1752 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1737 = false ∨ valuation q 1752 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1753 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1753)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 7 4 (meaning1717 q) (meaning1738 q) (meaning1753 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1738 = false ∨ valuation q 1753 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1754 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1754)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 7 5 (meaning1717 q) (meaning1739 q) (meaning1754 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1739 = false ∨ valuation q 1754 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1755 = true := by
  have hs : count1743 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) + (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81]) (l₂ := [-82, -84, -86, -87, -90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1740)) (literal (valuationOf q) (1755)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81]) (countLit q [-82, -84, -86, -87, -90, -91, -94, -95]) (count1743 q) 7 6 (meaning1717 q) (meaning1740 q) (meaning1755 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1740 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1740 = false ∨ valuation q 1755 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1759 = true := by
  have hs : count1759 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1759)) (countLit q [-96]) (countLit q [-99]) (count1759 q) 1 (meaningNeg99 q) (meaning1759 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1759 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1759 = true := by
  have hs : count1759 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1759)) (countLit q [-96]) (countLit q [-99]) (count1759 q) 1 (meaningNeg96 q) (meaning1759 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1759 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1760 = true := by
  have hs : count1759 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1760)) (countLit q [-96]) (countLit q [-99]) (count1759 q) 1 1 (meaningNeg96 q) (meaningNeg99 q) (meaning1760 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 1760 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1761 = true := by
  have hs : count1761 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1761)) (countLit q [-100]) (countLit q [-102]) (count1761 q) 1 (meaningNeg102 q) (meaning1761 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1761 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1761 = true := by
  have hs : count1761 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1761)) (countLit q [-100]) (countLit q [-102]) (count1761 q) 1 (meaningNeg100 q) (meaning1761 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1761 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1762 = true := by
  have hs : count1761 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1762)) (countLit q [-100]) (countLit q [-102]) (count1761 q) 1 1 (meaningNeg100 q) (meaningNeg102 q) (meaning1762 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 102 = true ∨ valuation q 1762 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1763 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_right (literal (valuationOf q) (1761)) (literal (valuationOf q) (1763)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 1 (meaning1761 q) (meaning1763 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1763 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1764 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_right (literal (valuationOf q) (1762)) (literal (valuationOf q) (1764)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 2 (meaning1762 q) (meaning1764 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1764 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1763 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_left (literal (valuationOf q) (1759)) (literal (valuationOf q) (1763)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 1 (meaning1759 q) (meaning1763 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1763 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1764 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1764)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 1 1 (meaning1759 q) (meaning1761 q) (meaning1764 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1761 = false ∨ valuation q 1764 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 1759 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1765 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_two (literal (valuationOf q) (1759)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1765)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 1 2 (meaning1759 q) (meaning1762 q) (meaning1765 q) hs
  change valuationOf q 1759 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 1759 = false ∨ valuation q 1762 = false ∨ valuation q 1765 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1764 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_left (literal (valuationOf q) (1760)) (literal (valuationOf q) (1764)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 2 (meaning1760 q) (meaning1764 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1764 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E052.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112052
