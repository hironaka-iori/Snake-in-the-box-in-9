import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1793 (q : Nat → Bool) : valuationOf q 1823 = false ∨ valuationOf q 1831 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1823)) (literal (valuationOf q) (1831)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 3 (meaning1823 q) (meaning1831 q) hs
  change valuationOf q 1823 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 1823 = false ∨ valuation q 1831 = true := counterClause1793 (baseVal q)

theorem counterClause1794 (q : Nat → Bool) : valuationOf q 1824 = false ∨ valuationOf q 1832 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1824)) (literal (valuationOf q) (1832)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 4 (meaning1824 q) (meaning1832 q) hs
  change valuationOf q 1824 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 1824 = false ∨ valuation q 1832 = true := counterClause1794 (baseVal q)

theorem counterClause1795 (q : Nat → Bool) : valuationOf q 1825 = false ∨ valuationOf q 1833 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1825)) (literal (valuationOf q) (1833)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 5 (meaning1825 q) (meaning1833 q) hs
  change valuationOf q 1825 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 1825 = false ∨ valuation q 1833 = true := counterClause1795 (baseVal q)

theorem counterClause1796 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1830 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1797)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1830)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 1 1 (meaning1797 q) (meaning1821 q) (meaning1830 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1821 = false ∨ valuation q 1830 = true := counterClause1796 (baseVal q)

theorem counterClause1797 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1831 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1797)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1831)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 1 2 (meaning1797 q) (meaning1822 q) (meaning1831 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1822 = false ∨ valuation q 1831 = true := counterClause1797 (baseVal q)

theorem counterClause1798 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1832 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1797)) (literal (valuationOf q) (1823)) (literal (valuationOf q) (1832)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 1 3 (meaning1797 q) (meaning1823 q) (meaning1832 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1823 = false ∨ valuation q 1832 = true := counterClause1798 (baseVal q)

theorem counterClause1799 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1833 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1797)) (literal (valuationOf q) (1824)) (literal (valuationOf q) (1833)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 1 4 (meaning1797 q) (meaning1824 q) (meaning1833 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1824 = false ∨ valuation q 1833 = true := counterClause1799 (baseVal q)

theorem counterClause1800 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1834 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1797)) (literal (valuationOf q) (1825)) (literal (valuationOf q) (1834)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 1 5 (meaning1797 q) (meaning1825 q) (meaning1834 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1825 = false ∨ valuation q 1834 = true := counterClause1800 (baseVal q)

theorem counterClause1801 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1835 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1797)) (literal (valuationOf q) (1826)) (literal (valuationOf q) (1835)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 1 6 (meaning1797 q) (meaning1826 q) (meaning1835 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1826 = false ∨ valuation q 1835 = true := counterClause1801 (baseVal q)

theorem counterClause1802 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1831 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1798)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1831)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 2 1 (meaning1798 q) (meaning1821 q) (meaning1831 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1821 = false ∨ valuation q 1831 = true := counterClause1802 (baseVal q)

theorem counterClause1803 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1832 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1798)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1832)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 2 2 (meaning1798 q) (meaning1822 q) (meaning1832 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1822 = false ∨ valuation q 1832 = true := counterClause1803 (baseVal q)

theorem counterClause1804 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1833 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1798)) (literal (valuationOf q) (1823)) (literal (valuationOf q) (1833)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 2 3 (meaning1798 q) (meaning1823 q) (meaning1833 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1823 = false ∨ valuation q 1833 = true := counterClause1804 (baseVal q)

theorem counterClause1805 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1834 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1798)) (literal (valuationOf q) (1824)) (literal (valuationOf q) (1834)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 2 4 (meaning1798 q) (meaning1824 q) (meaning1834 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1824 = false ∨ valuation q 1834 = true := counterClause1805 (baseVal q)

theorem counterClause1806 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1835 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1798)) (literal (valuationOf q) (1825)) (literal (valuationOf q) (1835)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 2 5 (meaning1798 q) (meaning1825 q) (meaning1835 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1825 = false ∨ valuation q 1835 = true := counterClause1806 (baseVal q)

theorem counterClause1807 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1836 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1798)) (literal (valuationOf q) (1826)) (literal (valuationOf q) (1836)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 2 6 (meaning1798 q) (meaning1826 q) (meaning1836 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1826 = false ∨ valuation q 1836 = true := counterClause1807 (baseVal q)

theorem counterClause1808 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1832 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1832)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 3 1 (meaning1799 q) (meaning1821 q) (meaning1832 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1821 = false ∨ valuation q 1832 = true := counterClause1808 (baseVal q)

theorem counterClause1809 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1833 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1833)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 3 2 (meaning1799 q) (meaning1822 q) (meaning1833 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1822 = false ∨ valuation q 1833 = true := counterClause1809 (baseVal q)

theorem counterClause1810 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1834 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1823)) (literal (valuationOf q) (1834)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 3 3 (meaning1799 q) (meaning1823 q) (meaning1834 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1823 = false ∨ valuation q 1834 = true := counterClause1810 (baseVal q)

theorem counterClause1811 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1835 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1824)) (literal (valuationOf q) (1835)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 3 4 (meaning1799 q) (meaning1824 q) (meaning1835 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1824 = false ∨ valuation q 1835 = true := counterClause1811 (baseVal q)

theorem counterClause1812 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1836 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1825)) (literal (valuationOf q) (1836)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 3 5 (meaning1799 q) (meaning1825 q) (meaning1836 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1825 = false ∨ valuation q 1836 = true := counterClause1812 (baseVal q)

theorem counterClause1813 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1837 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1826)) (literal (valuationOf q) (1837)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 3 6 (meaning1799 q) (meaning1826 q) (meaning1837 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1826 = false ∨ valuation q 1837 = true := counterClause1813 (baseVal q)

theorem counterClause1814 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1833 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1833)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 4 1 (meaning1800 q) (meaning1821 q) (meaning1833 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1821 = false ∨ valuation q 1833 = true := counterClause1814 (baseVal q)

theorem counterClause1815 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1834 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1834)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 4 2 (meaning1800 q) (meaning1822 q) (meaning1834 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1822 = false ∨ valuation q 1834 = true := counterClause1815 (baseVal q)

theorem counterClause1816 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1835 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1823)) (literal (valuationOf q) (1835)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 4 3 (meaning1800 q) (meaning1823 q) (meaning1835 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1816 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1823 = false ∨ valuation q 1835 = true := counterClause1816 (baseVal q)

theorem counterClause1817 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1836 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1824)) (literal (valuationOf q) (1836)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 4 4 (meaning1800 q) (meaning1824 q) (meaning1836 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1817 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1824 = false ∨ valuation q 1836 = true := counterClause1817 (baseVal q)

theorem counterClause1818 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1837 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1825)) (literal (valuationOf q) (1837)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 4 5 (meaning1800 q) (meaning1825 q) (meaning1837 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1818 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1825 = false ∨ valuation q 1837 = true := counterClause1818 (baseVal q)

theorem counterClause1819 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1838 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1826)) (literal (valuationOf q) (1838)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 4 6 (meaning1800 q) (meaning1826 q) (meaning1838 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1826 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1819 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1826 = false ∨ valuation q 1838 = true := counterClause1819 (baseVal q)

theorem counterClause1820 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1834 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1834)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 5 1 (meaning1801 q) (meaning1821 q) (meaning1834 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1820 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1821 = false ∨ valuation q 1834 = true := counterClause1820 (baseVal q)

theorem counterClause1821 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1835 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1835)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 5 2 (meaning1801 q) (meaning1822 q) (meaning1835 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1821 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1822 = false ∨ valuation q 1835 = true := counterClause1821 (baseVal q)

theorem counterClause1822 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1836 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1823)) (literal (valuationOf q) (1836)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 5 3 (meaning1801 q) (meaning1823 q) (meaning1836 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1823 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1822 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1823 = false ∨ valuation q 1836 = true := counterClause1822 (baseVal q)

theorem counterClause1823 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1837 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1824)) (literal (valuationOf q) (1837)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 5 4 (meaning1801 q) (meaning1824 q) (meaning1837 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1824 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1823 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1824 = false ∨ valuation q 1837 = true := counterClause1823 (baseVal q)

theorem counterClause1824 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1838 = true := by
  have hs : count1829 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -118, -120, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1825)) (literal (valuationOf q) (1838)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -118, -120, -121, -123, -125, -127]) (count1829 q) 5 5 (meaning1801 q) (meaning1825 q) (meaning1838 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1825 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1824 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1825 = false ∨ valuation q 1838 = true := counterClause1824 (baseVal q)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E055.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h, clause1816 q h, clause1817 q h, clause1818 q h, clause1819 q h, clause1820 q h, clause1821 q h, clause1822 q h, clause1823 q h, clause1824 q h⟩

end
end Snake9.Regrowth.E112055
