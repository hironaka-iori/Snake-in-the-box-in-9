import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1793 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1811 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1811)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 1 4 (meaning1775 q) (meaning1802 q) (meaning1811 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1802 = false ∨ valuation q 1811 = true := counterClause1793 (baseVal q)

theorem counterClause1794 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1812 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1803)) (literal (valuationOf q) (1812)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 1 5 (meaning1775 q) (meaning1803 q) (meaning1812 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1803 = false ∨ valuation q 1812 = true := counterClause1794 (baseVal q)

theorem counterClause1795 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1813 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1804)) (literal (valuationOf q) (1813)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 1 6 (meaning1775 q) (meaning1804 q) (meaning1813 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1804 = false ∨ valuation q 1813 = true := counterClause1795 (baseVal q)

theorem counterClause1796 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1776)) (literal (valuationOf q) (1808)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 (meaning1776 q) (meaning1808 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1808 = true := counterClause1796 (baseVal q)

theorem counterClause1797 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1809 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1809)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 1 (meaning1776 q) (meaning1799 q) (meaning1809 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1799 = false ∨ valuation q 1809 = true := counterClause1797 (baseVal q)

theorem counterClause1798 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1810 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1810)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 2 (meaning1776 q) (meaning1800 q) (meaning1810 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1800 = false ∨ valuation q 1810 = true := counterClause1798 (baseVal q)

theorem counterClause1799 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1811 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1801)) (literal (valuationOf q) (1811)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 3 (meaning1776 q) (meaning1801 q) (meaning1811 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1801 = false ∨ valuation q 1811 = true := counterClause1799 (baseVal q)

theorem counterClause1800 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1812 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1812)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 4 (meaning1776 q) (meaning1802 q) (meaning1812 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1802 = false ∨ valuation q 1812 = true := counterClause1800 (baseVal q)

theorem counterClause1801 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1813 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1803)) (literal (valuationOf q) (1813)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 5 (meaning1776 q) (meaning1803 q) (meaning1813 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1803 = false ∨ valuation q 1813 = true := counterClause1801 (baseVal q)

theorem counterClause1802 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1814 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1804)) (literal (valuationOf q) (1814)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 2 6 (meaning1776 q) (meaning1804 q) (meaning1814 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1804 = false ∨ valuation q 1814 = true := counterClause1802 (baseVal q)

theorem counterClause1803 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1809 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1777)) (literal (valuationOf q) (1809)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 (meaning1777 q) (meaning1809 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1809 = true := counterClause1803 (baseVal q)

theorem counterClause1804 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1810 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1810)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 1 (meaning1777 q) (meaning1799 q) (meaning1810 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1799 = false ∨ valuation q 1810 = true := counterClause1804 (baseVal q)

theorem counterClause1805 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1811 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1811)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 2 (meaning1777 q) (meaning1800 q) (meaning1811 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1800 = false ∨ valuation q 1811 = true := counterClause1805 (baseVal q)

theorem counterClause1806 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1812 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1801)) (literal (valuationOf q) (1812)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 3 (meaning1777 q) (meaning1801 q) (meaning1812 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1801 = false ∨ valuation q 1812 = true := counterClause1806 (baseVal q)

theorem counterClause1807 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1813 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1813)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 4 (meaning1777 q) (meaning1802 q) (meaning1813 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1802 = false ∨ valuation q 1813 = true := counterClause1807 (baseVal q)

theorem counterClause1808 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1814 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1803)) (literal (valuationOf q) (1814)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 5 (meaning1777 q) (meaning1803 q) (meaning1814 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1803 = false ∨ valuation q 1814 = true := counterClause1808 (baseVal q)

theorem counterClause1809 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1815 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1804)) (literal (valuationOf q) (1815)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 3 6 (meaning1777 q) (meaning1804 q) (meaning1815 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1804 = false ∨ valuation q 1815 = true := counterClause1809 (baseVal q)

theorem counterClause1810 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1810 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1778)) (literal (valuationOf q) (1810)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 (meaning1778 q) (meaning1810 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1810 = true := counterClause1810 (baseVal q)

theorem counterClause1811 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1811 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1811)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 1 (meaning1778 q) (meaning1799 q) (meaning1811 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1799 = false ∨ valuation q 1811 = true := counterClause1811 (baseVal q)

theorem counterClause1812 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1812 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1812)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 2 (meaning1778 q) (meaning1800 q) (meaning1812 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1800 = false ∨ valuation q 1812 = true := counterClause1812 (baseVal q)

theorem counterClause1813 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1813 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1801)) (literal (valuationOf q) (1813)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 3 (meaning1778 q) (meaning1801 q) (meaning1813 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1801 = false ∨ valuation q 1813 = true := counterClause1813 (baseVal q)

theorem counterClause1814 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1814 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1814)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 4 (meaning1778 q) (meaning1802 q) (meaning1814 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1802 = false ∨ valuation q 1814 = true := counterClause1814 (baseVal q)

theorem counterClause1815 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1815 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1803)) (literal (valuationOf q) (1815)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 5 (meaning1778 q) (meaning1803 q) (meaning1815 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1803 = false ∨ valuation q 1815 = true := counterClause1815 (baseVal q)

theorem counterClause1816 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1816 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1804)) (literal (valuationOf q) (1816)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 4 6 (meaning1778 q) (meaning1804 q) (meaning1816 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1804 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1816 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1804 = false ∨ valuation q 1816 = true := counterClause1816 (baseVal q)

theorem counterClause1817 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1811 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1779)) (literal (valuationOf q) (1811)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 5 (meaning1779 q) (meaning1811 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1817 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1811 = true := counterClause1817 (baseVal q)

theorem counterClause1818 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1812 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1812)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 5 1 (meaning1779 q) (meaning1799 q) (meaning1812 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1818 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1799 = false ∨ valuation q 1812 = true := counterClause1818 (baseVal q)

theorem counterClause1819 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1813 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1813)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 5 2 (meaning1779 q) (meaning1800 q) (meaning1813 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1819 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1800 = false ∨ valuation q 1813 = true := counterClause1819 (baseVal q)

theorem counterClause1820 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1814 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1801)) (literal (valuationOf q) (1814)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 5 3 (meaning1779 q) (meaning1801 q) (meaning1814 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1820 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1801 = false ∨ valuation q 1814 = true := counterClause1820 (baseVal q)

theorem counterClause1821 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1815 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1815)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 5 4 (meaning1779 q) (meaning1802 q) (meaning1815 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1821 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1802 = false ∨ valuation q 1815 = true := counterClause1821 (baseVal q)

theorem counterClause1822 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1816 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1803)) (literal (valuationOf q) (1816)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 5 5 (meaning1779 q) (meaning1803 q) (meaning1816 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1822 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1803 = false ∨ valuation q 1816 = true := counterClause1822 (baseVal q)

theorem counterClause1823 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1812 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1780)) (literal (valuationOf q) (1812)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 6 (meaning1780 q) (meaning1812 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1823 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1812 = true := counterClause1823 (baseVal q)

theorem counterClause1824 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1813 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1813)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 6 1 (meaning1780 q) (meaning1799 q) (meaning1813 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1824 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1799 = false ∨ valuation q 1813 = true := counterClause1824 (baseVal q)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E052.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h, clause1816 q h, clause1817 q h, clause1818 q h, clause1819 q h, clause1820 q h, clause1821 q h, clause1822 q h, clause1823 q h, clause1824 q h⟩

end
end Snake9.Regrowth.E112052
