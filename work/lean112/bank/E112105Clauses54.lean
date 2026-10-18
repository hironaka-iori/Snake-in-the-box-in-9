import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1753 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1753)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 2 1 (meaning1740 q) (meaning1747 q) (meaning1753 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1747 = false ∨ valuation q 1753 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1754 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1754)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 2 2 (meaning1740 q) (meaning1748 q) (meaning1754 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1748 = false ∨ valuation q 1754 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1755 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1755)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 2 3 (meaning1740 q) (meaning1749 q) (meaning1755 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1749 = false ∨ valuation q 1755 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1756 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1756)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 2 4 (meaning1740 q) (meaning1750 q) (meaning1756 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1750 = false ∨ valuation q 1756 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1753 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1741)) (literal (valuationOf q) (1753)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 3 (meaning1741 q) (meaning1753 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1753 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1754 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1754)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 3 1 (meaning1741 q) (meaning1747 q) (meaning1754 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1747 = false ∨ valuation q 1754 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1755 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1755)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 3 2 (meaning1741 q) (meaning1748 q) (meaning1755 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1748 = false ∨ valuation q 1755 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1756 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1756)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 3 3 (meaning1741 q) (meaning1749 q) (meaning1756 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1749 = false ∨ valuation q 1756 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1757 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1757)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 3 4 (meaning1741 q) (meaning1750 q) (meaning1757 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1750 = false ∨ valuation q 1757 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1754 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1742)) (literal (valuationOf q) (1754)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 4 (meaning1742 q) (meaning1754 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1754 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1755 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1755)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 4 1 (meaning1742 q) (meaning1747 q) (meaning1755 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1747 = false ∨ valuation q 1755 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1756 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1756)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 4 2 (meaning1742 q) (meaning1748 q) (meaning1756 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1748 = false ∨ valuation q 1756 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1757 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1757)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 4 3 (meaning1742 q) (meaning1749 q) (meaning1757 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1749 = false ∨ valuation q 1757 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1758 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1758)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 4 4 (meaning1742 q) (meaning1750 q) (meaning1758 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1750 = false ∨ valuation q 1758 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1763 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1755)) (literal (valuationOf q) (1763)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 (meaning1755 q) (meaning1763 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1763 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1764 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1756)) (literal (valuationOf q) (1764)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 (meaning1756 q) (meaning1764 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1764 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 1757 = false ∨ valuationOf q 1765 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1757)) (literal (valuationOf q) (1765)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 7 (meaning1757 q) (meaning1765 q) hs
  change valuationOf q 1757 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 1757 = false ∨ valuation q 1765 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1762 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1762)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 1 3 (meaning1727 q) (meaning1753 q) (meaning1762 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1753 = false ∨ valuation q 1762 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1763 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1763)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 1 4 (meaning1727 q) (meaning1754 q) (meaning1763 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1754 = false ∨ valuation q 1763 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1764 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1764)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 1 5 (meaning1727 q) (meaning1755 q) (meaning1764 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1755 = false ∨ valuation q 1764 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1765 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1765)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 1 6 (meaning1727 q) (meaning1756 q) (meaning1765 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1756 = false ∨ valuation q 1765 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1766 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1766)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 1 7 (meaning1727 q) (meaning1757 q) (meaning1766 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1757 = false ∨ valuation q 1766 = true := counterClause1750 (baseVal q)

theorem counterClause1751 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1762 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1762)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 2 2 (meaning1728 q) (meaning1752 q) (meaning1762 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1752 = false ∨ valuation q 1762 = true := counterClause1751 (baseVal q)

theorem counterClause1752 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1763 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1763)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 2 3 (meaning1728 q) (meaning1753 q) (meaning1763 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1753 = false ∨ valuation q 1763 = true := counterClause1752 (baseVal q)

theorem counterClause1753 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1764 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1764)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 2 4 (meaning1728 q) (meaning1754 q) (meaning1764 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1754 = false ∨ valuation q 1764 = true := counterClause1753 (baseVal q)

theorem counterClause1754 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1765 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1765)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 2 5 (meaning1728 q) (meaning1755 q) (meaning1765 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1755 = false ∨ valuation q 1765 = true := counterClause1754 (baseVal q)

theorem counterClause1755 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1766 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1766)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 2 6 (meaning1728 q) (meaning1756 q) (meaning1766 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1756 = false ∨ valuation q 1766 = true := counterClause1755 (baseVal q)

theorem counterClause1756 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1767 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1767)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 2 7 (meaning1728 q) (meaning1757 q) (meaning1767 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1757 = false ∨ valuation q 1767 = true := counterClause1756 (baseVal q)

theorem counterClause1757 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1768 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1768)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 2 8 (meaning1728 q) (meaning1758 q) (meaning1768 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1758 = false ∨ valuation q 1768 = true := counterClause1757 (baseVal q)

theorem counterClause1758 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1762)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 1 (meaning1729 q) (meaning1751 q) (meaning1762 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1751 = false ∨ valuation q 1762 = true := counterClause1758 (baseVal q)

theorem counterClause1759 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1763 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1763)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 2 (meaning1729 q) (meaning1752 q) (meaning1763 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1752 = false ∨ valuation q 1763 = true := counterClause1759 (baseVal q)

theorem counterClause1760 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1764 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1764)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 3 (meaning1729 q) (meaning1753 q) (meaning1764 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1753 = false ∨ valuation q 1764 = true := counterClause1760 (baseVal q)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E105.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112105
