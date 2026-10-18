import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1761 (q : Nat → Bool) : valuationOf q 127 = true ∨ valuationOf q 1815 = true := by
  have hs : count1815 q = (countLit q [-125]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-127])
  have hm := merge_right (literal (valuationOf q) (-127)) (literal (valuationOf q) (1815)) (countLit q [-125]) (countLit q [-127]) (count1815 q) 1 (meaningNeg127 q) (meaning1815 q) hs
  change (! (valuationOf q 127)) = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 127 = true ∨ valuation q 1815 = true := counterClause1761 (baseVal q)

theorem counterClause1762 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 1815 = true := by
  have hs : count1815 q = (countLit q [-125]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-127])
  have hm := merge_left (literal (valuationOf q) (-125)) (literal (valuationOf q) (1815)) (countLit q [-125]) (countLit q [-127]) (count1815 q) 1 (meaningNeg125 q) (meaning1815 q) hs
  change (! (valuationOf q 125)) = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 1815 = true := counterClause1762 (baseVal q)

theorem counterClause1763 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 127 = true ∨ valuationOf q 1816 = true := by
  have hs : count1815 q = (countLit q [-125]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-127])
  have hm := merge_two (literal (valuationOf q) (-125)) (literal (valuationOf q) (-127)) (literal (valuationOf q) (1816)) (countLit q [-125]) (countLit q [-127]) (count1815 q) 1 1 (meaningNeg125 q) (meaningNeg127 q) (meaning1816 q) hs
  change (! (valuationOf q 125)) = false ∨ (! (valuationOf q 127)) = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 127 = true ∨ valuation q 1816 = true := counterClause1763 (baseVal q)

theorem counterClause1764 (q : Nat → Bool) : valuationOf q 1815 = false ∨ valuationOf q 1817 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_right (literal (valuationOf q) (1815)) (literal (valuationOf q) (1817)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 1 (meaning1815 q) (meaning1817 q) hs
  change valuationOf q 1815 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 1815 = false ∨ valuation q 1817 = true := counterClause1764 (baseVal q)

theorem counterClause1765 (q : Nat → Bool) : valuationOf q 1816 = false ∨ valuationOf q 1818 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_right (literal (valuationOf q) (1816)) (literal (valuationOf q) (1818)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 2 (meaning1816 q) (meaning1818 q) hs
  change valuationOf q 1816 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 1816 = false ∨ valuation q 1818 = true := counterClause1765 (baseVal q)

theorem counterClause1766 (q : Nat → Bool) : valuationOf q 1813 = false ∨ valuationOf q 1817 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_left (literal (valuationOf q) (1813)) (literal (valuationOf q) (1817)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 1 (meaning1813 q) (meaning1817 q) hs
  change valuationOf q 1813 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 1813 = false ∨ valuation q 1817 = true := counterClause1766 (baseVal q)

theorem counterClause1767 (q : Nat → Bool) : valuationOf q 1813 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1818 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_two (literal (valuationOf q) (1813)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1818)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 1 1 (meaning1813 q) (meaning1815 q) (meaning1818 q) hs
  change valuationOf q 1813 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 1813 = false ∨ valuation q 1815 = false ∨ valuation q 1818 = true := counterClause1767 (baseVal q)

theorem counterClause1768 (q : Nat → Bool) : valuationOf q 1813 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1819 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_two (literal (valuationOf q) (1813)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1819)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 1 2 (meaning1813 q) (meaning1816 q) (meaning1819 q) hs
  change valuationOf q 1813 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 1813 = false ∨ valuation q 1816 = false ∨ valuation q 1819 = true := counterClause1768 (baseVal q)

theorem counterClause1769 (q : Nat → Bool) : valuationOf q 1814 = false ∨ valuationOf q 1818 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_left (literal (valuationOf q) (1814)) (literal (valuationOf q) (1818)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 2 (meaning1814 q) (meaning1818 q) hs
  change valuationOf q 1814 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 1814 = false ∨ valuation q 1818 = true := counterClause1769 (baseVal q)

theorem counterClause1770 (q : Nat → Bool) : valuationOf q 1814 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1819 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_two (literal (valuationOf q) (1814)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1819)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 2 1 (meaning1814 q) (meaning1815 q) (meaning1819 q) hs
  change valuationOf q 1814 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 1814 = false ∨ valuation q 1815 = false ∨ valuation q 1819 = true := counterClause1770 (baseVal q)

theorem counterClause1771 (q : Nat → Bool) : valuationOf q 1814 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1820 = true := by
  have hs : count1817 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_two (literal (valuationOf q) (1814)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1820)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1817 q) 2 2 (meaning1814 q) (meaning1816 q) (meaning1820 q) hs
  change valuationOf q 1814 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 1814 = false ∨ valuation q 1816 = false ∨ valuation q 1820 = true := counterClause1771 (baseVal q)

theorem counterClause1772 (q : Nat → Bool) : valuationOf q 1817 = false ∨ valuationOf q 1821 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1817)) (literal (valuationOf q) (1821)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 1 (meaning1817 q) (meaning1821 q) hs
  change valuationOf q 1817 = false ∨ valuationOf q 1821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 1817 = false ∨ valuation q 1821 = true := counterClause1772 (baseVal q)

theorem counterClause1773 (q : Nat → Bool) : valuationOf q 1818 = false ∨ valuationOf q 1822 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1818)) (literal (valuationOf q) (1822)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 2 (meaning1818 q) (meaning1822 q) hs
  change valuationOf q 1818 = false ∨ valuationOf q 1822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 1818 = false ∨ valuation q 1822 = true := counterClause1773 (baseVal q)

theorem counterClause1774 (q : Nat → Bool) : valuationOf q 1819 = false ∨ valuationOf q 1823 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1819)) (literal (valuationOf q) (1823)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 3 (meaning1819 q) (meaning1823 q) hs
  change valuationOf q 1819 = false ∨ valuationOf q 1823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 1819 = false ∨ valuation q 1823 = true := counterClause1774 (baseVal q)

theorem counterClause1775 (q : Nat → Bool) : valuationOf q 1820 = false ∨ valuationOf q 1824 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1820)) (literal (valuationOf q) (1824)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 4 (meaning1820 q) (meaning1824 q) hs
  change valuationOf q 1820 = false ∨ valuationOf q 1824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 1820 = false ∨ valuation q 1824 = true := counterClause1775 (baseVal q)

theorem counterClause1776 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1821 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1809)) (literal (valuationOf q) (1821)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 1 (meaning1809 q) (meaning1821 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1821 = true := counterClause1776 (baseVal q)

theorem counterClause1777 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1822 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1809)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1822)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 1 1 (meaning1809 q) (meaning1817 q) (meaning1822 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1817 = false ∨ valuation q 1822 = true := counterClause1777 (baseVal q)

theorem counterClause1778 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1823 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1809)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1823)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 1 2 (meaning1809 q) (meaning1818 q) (meaning1823 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1818 = false ∨ valuation q 1823 = true := counterClause1778 (baseVal q)

theorem counterClause1779 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1824 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1809)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1824)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 1 3 (meaning1809 q) (meaning1819 q) (meaning1824 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1819 = false ∨ valuation q 1824 = true := counterClause1779 (baseVal q)

theorem counterClause1780 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1825 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1809)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1825)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 1 4 (meaning1809 q) (meaning1820 q) (meaning1825 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1820 = false ∨ valuation q 1825 = true := counterClause1780 (baseVal q)

theorem counterClause1781 (q : Nat → Bool) : valuationOf q 1810 = false ∨ valuationOf q 1822 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1810)) (literal (valuationOf q) (1822)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 2 (meaning1810 q) (meaning1822 q) hs
  change valuationOf q 1810 = false ∨ valuationOf q 1822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 1810 = false ∨ valuation q 1822 = true := counterClause1781 (baseVal q)

theorem counterClause1782 (q : Nat → Bool) : valuationOf q 1810 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1823 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1810)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1823)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 2 1 (meaning1810 q) (meaning1817 q) (meaning1823 q) hs
  change valuationOf q 1810 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 1810 = false ∨ valuation q 1817 = false ∨ valuation q 1823 = true := counterClause1782 (baseVal q)

theorem counterClause1783 (q : Nat → Bool) : valuationOf q 1810 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1824 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1810)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1824)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 2 2 (meaning1810 q) (meaning1818 q) (meaning1824 q) hs
  change valuationOf q 1810 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 1810 = false ∨ valuation q 1818 = false ∨ valuation q 1824 = true := counterClause1783 (baseVal q)

theorem counterClause1784 (q : Nat → Bool) : valuationOf q 1810 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1825 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1810)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1825)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 2 3 (meaning1810 q) (meaning1819 q) (meaning1825 q) hs
  change valuationOf q 1810 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 1810 = false ∨ valuation q 1819 = false ∨ valuation q 1825 = true := counterClause1784 (baseVal q)

theorem counterClause1785 (q : Nat → Bool) : valuationOf q 1811 = false ∨ valuationOf q 1823 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1811)) (literal (valuationOf q) (1823)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 3 (meaning1811 q) (meaning1823 q) hs
  change valuationOf q 1811 = false ∨ valuationOf q 1823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 1811 = false ∨ valuation q 1823 = true := counterClause1785 (baseVal q)

theorem counterClause1786 (q : Nat → Bool) : valuationOf q 1811 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1824 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1811)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1824)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 3 1 (meaning1811 q) (meaning1817 q) (meaning1824 q) hs
  change valuationOf q 1811 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 1811 = false ∨ valuation q 1817 = false ∨ valuation q 1824 = true := counterClause1786 (baseVal q)

theorem counterClause1787 (q : Nat → Bool) : valuationOf q 1811 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1825 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1811)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1825)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 3 2 (meaning1811 q) (meaning1818 q) (meaning1825 q) hs
  change valuationOf q 1811 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 1811 = false ∨ valuation q 1818 = false ∨ valuation q 1825 = true := counterClause1787 (baseVal q)

theorem counterClause1788 (q : Nat → Bool) : valuationOf q 1811 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1826 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1811)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1826)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 3 3 (meaning1811 q) (meaning1819 q) (meaning1826 q) hs
  change valuationOf q 1811 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 1811 = false ∨ valuation q 1819 = false ∨ valuation q 1826 = true := counterClause1788 (baseVal q)

theorem counterClause1789 (q : Nat → Bool) : valuationOf q 1812 = false ∨ valuationOf q 1824 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1812)) (literal (valuationOf q) (1824)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 4 (meaning1812 q) (meaning1824 q) hs
  change valuationOf q 1812 = false ∨ valuationOf q 1824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 1812 = false ∨ valuation q 1824 = true := counterClause1789 (baseVal q)

theorem counterClause1790 (q : Nat → Bool) : valuationOf q 1812 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1825 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1812)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1825)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 4 1 (meaning1812 q) (meaning1817 q) (meaning1825 q) hs
  change valuationOf q 1812 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 1812 = false ∨ valuation q 1817 = false ∨ valuation q 1825 = true := counterClause1790 (baseVal q)

theorem counterClause1791 (q : Nat → Bool) : valuationOf q 1812 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1826 = true := by
  have hs : count1821 q = (countLit q [-115, -116, -118, -120]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -118, -120]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1812)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1826)) (countLit q [-115, -116, -118, -120]) (countLit q [-121, -123, -125, -127]) (count1821 q) 4 2 (meaning1812 q) (meaning1818 q) (meaning1826 q) hs
  change valuationOf q 1812 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 1812 = false ∨ valuation q 1818 = false ∨ valuation q 1826 = true := counterClause1791 (baseVal q)

theorem counterClause1792 (q : Nat → Bool) : valuationOf q 1822 = false ∨ valuationOf q 1830 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1822)) (literal (valuationOf q) (1830)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 2 (meaning1822 q) (meaning1830 q) hs
  change valuationOf q 1822 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 1822 = false ∨ valuation q 1830 = true := counterClause1792 (baseVal q)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E055.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112055
