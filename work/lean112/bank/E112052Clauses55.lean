import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1761 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1796 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_left (literal (valuationOf q) (1792)) (literal (valuationOf q) (1796)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 2 (meaning1792 q) (meaning1796 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1796 = true := counterClause1761 (baseVal q)

theorem counterClause1762 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1797 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1797)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 2 1 (meaning1792 q) (meaning1793 q) (meaning1797 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1793 = false ∨ valuation q 1797 = true := counterClause1762 (baseVal q)

theorem counterClause1763 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1798 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1794)) (literal (valuationOf q) (1798)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 2 2 (meaning1792 q) (meaning1794 q) (meaning1798 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1794 = false ∨ valuation q 1798 = true := counterClause1763 (baseVal q)

theorem counterClause1764 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1795)) (literal (valuationOf q) (1799)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 1 (meaning1795 q) (meaning1799 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1799 = true := counterClause1764 (baseVal q)

theorem counterClause1765 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1796)) (literal (valuationOf q) (1800)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 2 (meaning1796 q) (meaning1800 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1800 = true := counterClause1765 (baseVal q)

theorem counterClause1766 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1797)) (literal (valuationOf q) (1801)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 3 (meaning1797 q) (meaning1801 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1801 = true := counterClause1766 (baseVal q)

theorem counterClause1767 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1798)) (literal (valuationOf q) (1802)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 4 (meaning1798 q) (meaning1802 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1802 = true := counterClause1767 (baseVal q)

theorem counterClause1768 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1787)) (literal (valuationOf q) (1799)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 1 (meaning1787 q) (meaning1799 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1799 = true := counterClause1768 (baseVal q)

theorem counterClause1769 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1800)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 1 1 (meaning1787 q) (meaning1795 q) (meaning1800 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1795 = false ∨ valuation q 1800 = true := counterClause1769 (baseVal q)

theorem counterClause1770 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1796)) (literal (valuationOf q) (1801)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 1 2 (meaning1787 q) (meaning1796 q) (meaning1801 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1796 = false ∨ valuation q 1801 = true := counterClause1770 (baseVal q)

theorem counterClause1771 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1802)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 1 3 (meaning1787 q) (meaning1797 q) (meaning1802 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1797 = false ∨ valuation q 1802 = true := counterClause1771 (baseVal q)

theorem counterClause1772 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1803 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1803)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 1 4 (meaning1787 q) (meaning1798 q) (meaning1803 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1798 = false ∨ valuation q 1803 = true := counterClause1772 (baseVal q)

theorem counterClause1773 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1788)) (literal (valuationOf q) (1800)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 2 (meaning1788 q) (meaning1800 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1800 = true := counterClause1773 (baseVal q)

theorem counterClause1774 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1801)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 2 1 (meaning1788 q) (meaning1795 q) (meaning1801 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1795 = false ∨ valuation q 1801 = true := counterClause1774 (baseVal q)

theorem counterClause1775 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1796)) (literal (valuationOf q) (1802)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 2 2 (meaning1788 q) (meaning1796 q) (meaning1802 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1796 = false ∨ valuation q 1802 = true := counterClause1775 (baseVal q)

theorem counterClause1776 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1803 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1803)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 2 3 (meaning1788 q) (meaning1797 q) (meaning1803 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1797 = false ∨ valuation q 1803 = true := counterClause1776 (baseVal q)

theorem counterClause1777 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1804 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1804)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 2 4 (meaning1788 q) (meaning1798 q) (meaning1804 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1798 = false ∨ valuation q 1804 = true := counterClause1777 (baseVal q)

theorem counterClause1778 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1789)) (literal (valuationOf q) (1801)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 3 (meaning1789 q) (meaning1801 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1801 = true := counterClause1778 (baseVal q)

theorem counterClause1779 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1802)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 3 1 (meaning1789 q) (meaning1795 q) (meaning1802 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1795 = false ∨ valuation q 1802 = true := counterClause1779 (baseVal q)

theorem counterClause1780 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1803 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1796)) (literal (valuationOf q) (1803)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 3 2 (meaning1789 q) (meaning1796 q) (meaning1803 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1796 = false ∨ valuation q 1803 = true := counterClause1780 (baseVal q)

theorem counterClause1781 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1804 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1804)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 3 3 (meaning1789 q) (meaning1797 q) (meaning1804 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1797 = false ∨ valuation q 1804 = true := counterClause1781 (baseVal q)

theorem counterClause1782 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1790)) (literal (valuationOf q) (1802)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 4 (meaning1790 q) (meaning1802 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1802 = true := counterClause1782 (baseVal q)

theorem counterClause1783 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1803 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1803)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 4 1 (meaning1790 q) (meaning1795 q) (meaning1803 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1795 = false ∨ valuation q 1803 = true := counterClause1783 (baseVal q)

theorem counterClause1784 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1804 = true := by
  have hs : count1799 q = (countLit q [-112, -114, -118, -120]) + (countLit q [-122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -118, -120]) (l₂ := [-122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1796)) (literal (valuationOf q) (1804)) (countLit q [-112, -114, -118, -120]) (countLit q [-122, -123, -126, -127]) (count1799 q) 4 2 (meaning1790 q) (meaning1796 q) (meaning1804 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1796 = false ∨ valuation q 1804 = true := counterClause1784 (baseVal q)

theorem counterClause1785 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1800)) (literal (valuationOf q) (1808)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 (meaning1800 q) (meaning1808 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1808 = true := counterClause1785 (baseVal q)

theorem counterClause1786 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1809 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1801)) (literal (valuationOf q) (1809)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 (meaning1801 q) (meaning1809 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1809 = true := counterClause1786 (baseVal q)

theorem counterClause1787 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1810 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1802)) (literal (valuationOf q) (1810)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 (meaning1802 q) (meaning1810 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1810 = true := counterClause1787 (baseVal q)

theorem counterClause1788 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1811 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1803)) (literal (valuationOf q) (1811)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 5 (meaning1803 q) (meaning1811 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1811 = true := counterClause1788 (baseVal q)

theorem counterClause1789 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1775)) (literal (valuationOf q) (1807)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 1 (meaning1775 q) (meaning1807 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1807 = true := counterClause1789 (baseVal q)

theorem counterClause1790 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1808)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 1 1 (meaning1775 q) (meaning1799 q) (meaning1808 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1799 = false ∨ valuation q 1808 = true := counterClause1790 (baseVal q)

theorem counterClause1791 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1809 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1809)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 1 2 (meaning1775 q) (meaning1800 q) (meaning1809 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1800 = false ∨ valuation q 1809 = true := counterClause1791 (baseVal q)

theorem counterClause1792 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1810 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1801)) (literal (valuationOf q) (1810)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 1 3 (meaning1775 q) (meaning1801 q) (meaning1810 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1801 = false ∨ valuation q 1810 = true := counterClause1792 (baseVal q)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E052.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112052
