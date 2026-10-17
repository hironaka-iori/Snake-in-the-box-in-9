import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1794 = true := by
  have hs : count1787 q = (countLit q [-96, -97, -100, -101]) + (countLit q [-103, -104, -108, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -100, -101]) (l₂ := [-103, -104, -108, -109])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1794)) (countLit q [-96, -97, -100, -101]) (countLit q [-103, -104, -108, -109]) (count1787 q) 4 4 (meaning1778 q) (meaning1786 q) (meaning1794 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1786 = false ∨ valuation q 1794 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1795)) (countLit q [-111]) (countLit q [-113]) (count1795 q) 1 (meaningNeg113 q) (meaning1795 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1795 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1795)) (countLit q [-111]) (countLit q [-113]) (count1795 q) 1 (meaningNeg111 q) (meaning1795 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1795 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1796 = true := by
  have hs : count1795 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1796)) (countLit q [-111]) (countLit q [-113]) (count1795 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1796 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1796 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1796 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-115]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1797)) (countLit q [-115]) (countLit q [-119]) (count1797 q) 1 (meaningNeg119 q) (meaning1797 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1797 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-115]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-119])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1797)) (countLit q [-115]) (countLit q [-119]) (count1797 q) 1 (meaningNeg115 q) (meaning1797 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1797 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 119 = true ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-115]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-119])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-119)) (literal (valuationOf q) (1798)) (countLit q [-115]) (countLit q [-119]) (count1797 q) 1 1 (meaningNeg115 q) (meaningNeg119 q) (meaning1798 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 119)) = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 119 = true ∨ valuation q 1798 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_right (literal (valuationOf q) (1797)) (literal (valuationOf q) (1799)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 1 (meaning1797 q) (meaning1799 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1799 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_right (literal (valuationOf q) (1798)) (literal (valuationOf q) (1800)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 2 (meaning1798 q) (meaning1800 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1800 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_left (literal (valuationOf q) (1795)) (literal (valuationOf q) (1799)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 1 (meaning1795 q) (meaning1799 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1799 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_two (literal (valuationOf q) (1795)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1800)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 1 1 (meaning1795 q) (meaning1797 q) (meaning1800 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1797 = false ∨ valuation q 1800 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_two (literal (valuationOf q) (1795)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1801)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 1 2 (meaning1795 q) (meaning1798 q) (meaning1801 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1798 = false ∨ valuation q 1801 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_left (literal (valuationOf q) (1796)) (literal (valuationOf q) (1800)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 2 (meaning1796 q) (meaning1800 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1800 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_two (literal (valuationOf q) (1796)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1801)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 2 1 (meaning1796 q) (meaning1797 q) (meaning1801 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1797 = false ∨ valuation q 1801 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-111, -113]) + (countLit q [-115, -119]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -119])
  have hm := merge_two (literal (valuationOf q) (1796)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1802)) (countLit q [-111, -113]) (countLit q [-115, -119]) (count1799 q) 2 2 (meaning1796 q) (meaning1798 q) (meaning1802 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1798 = false ∨ valuation q 1802 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1803 = true := by
  have hs : count1803 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1803)) (countLit q [-121]) (countLit q [-123]) (count1803 q) 1 (meaningNeg123 q) (meaning1803 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1803 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1803 = true := by
  have hs : count1803 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-121)) (literal (valuationOf q) (1803)) (countLit q [-121]) (countLit q [-123]) (count1803 q) 1 (meaningNeg121 q) (meaning1803 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1803 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1804 = true := by
  have hs : count1803 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-121)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1804)) (countLit q [-121]) (countLit q [-123]) (count1803 q) 1 1 (meaningNeg121 q) (meaningNeg123 q) (meaning1804 q) hs
  change (! (valuationOf q 121)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 123 = true ∨ valuation q 1804 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 128 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-127]) + (countLit q [-128]) := List.countP_append (p := literal q) (l₁ := [-127]) (l₂ := [-128])
  have hm := merge_right (literal (valuationOf q) (-128)) (literal (valuationOf q) (1805)) (countLit q [-127]) (countLit q [-128]) (count1805 q) 1 (meaningNeg128 q) (meaning1805 q) hs
  change (! (valuationOf q 128)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 128 = true ∨ valuation q 1805 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 127 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-127]) + (countLit q [-128]) := List.countP_append (p := literal q) (l₁ := [-127]) (l₂ := [-128])
  have hm := merge_left (literal (valuationOf q) (-127)) (literal (valuationOf q) (1805)) (countLit q [-127]) (countLit q [-128]) (count1805 q) 1 (meaningNeg127 q) (meaning1805 q) hs
  change (! (valuationOf q 127)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 127 = true ∨ valuation q 1805 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 127 = true ∨ valuationOf q 128 = true ∨ valuationOf q 1806 = true := by
  have hs : count1805 q = (countLit q [-127]) + (countLit q [-128]) := List.countP_append (p := literal q) (l₁ := [-127]) (l₂ := [-128])
  have hm := merge_two (literal (valuationOf q) (-127)) (literal (valuationOf q) (-128)) (literal (valuationOf q) (1806)) (countLit q [-127]) (countLit q [-128]) (count1805 q) 1 1 (meaningNeg127 q) (meaningNeg128 q) (meaning1806 q) hs
  change (! (valuationOf q 127)) = false ∨ (! (valuationOf q 128)) = false ∨ valuationOf q 1806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 1806 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1805 = false ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-127, -128]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-127, -128])
  have hm := merge_right (literal (valuationOf q) (1805)) (literal (valuationOf q) (1807)) (countLit q [-124]) (countLit q [-127, -128]) (count1807 q) 1 (meaning1805 q) (meaning1807 q) hs
  change valuationOf q 1805 = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1805 = false ∨ valuation q 1807 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1806 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-127, -128]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-127, -128])
  have hm := merge_right (literal (valuationOf q) (1806)) (literal (valuationOf q) (1808)) (countLit q [-124]) (countLit q [-127, -128]) (count1807 q) 2 (meaning1806 q) (meaning1808 q) hs
  change valuationOf q 1806 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1806 = false ∨ valuation q 1808 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-127, -128]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-127, -128])
  have hm := merge_left (literal (valuationOf q) (-124)) (literal (valuationOf q) (1807)) (countLit q [-124]) (countLit q [-127, -128]) (count1807 q) 1 (meaningNeg124 q) (meaning1807 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1807 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1805 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-127, -128]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-127, -128])
  have hm := merge_two (literal (valuationOf q) (-124)) (literal (valuationOf q) (1805)) (literal (valuationOf q) (1808)) (countLit q [-124]) (countLit q [-127, -128]) (count1807 q) 1 1 (meaningNeg124 q) (meaning1805 q) (meaning1808 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1805 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1805 = false ∨ valuation q 1808 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1806 = false ∨ valuationOf q 1809 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-127, -128]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-127, -128])
  have hm := merge_two (literal (valuationOf q) (-124)) (literal (valuationOf q) (1806)) (literal (valuationOf q) (1809)) (countLit q [-124]) (countLit q [-127, -128]) (count1807 q) 1 2 (meaningNeg124 q) (meaning1806 q) (meaning1809 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1806 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1806 = false ∨ valuation q 1809 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 1807 = false ∨ valuationOf q 1810 = true := by
  have hs : count1810 q = (countLit q [-121, -123]) + (countLit q [-124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-124, -127, -128])
  have hm := merge_right (literal (valuationOf q) (1807)) (literal (valuationOf q) (1810)) (countLit q [-121, -123]) (countLit q [-124, -127, -128]) (count1810 q) 1 (meaning1807 q) (meaning1810 q) hs
  change valuationOf q 1807 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 1807 = false ∨ valuation q 1810 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 1808 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-121, -123]) + (countLit q [-124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-124, -127, -128])
  have hm := merge_right (literal (valuationOf q) (1808)) (literal (valuationOf q) (1811)) (countLit q [-121, -123]) (countLit q [-124, -127, -128]) (count1810 q) 2 (meaning1808 q) (meaning1811 q) hs
  change valuationOf q 1808 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 1808 = false ∨ valuation q 1811 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-121, -123]) + (countLit q [-124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-124, -127, -128])
  have hm := merge_right (literal (valuationOf q) (1809)) (literal (valuationOf q) (1812)) (countLit q [-121, -123]) (countLit q [-124, -127, -128]) (count1810 q) 3 (meaning1809 q) (meaning1812 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1812 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1810 = true := by
  have hs : count1810 q = (countLit q [-121, -123]) + (countLit q [-124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-124, -127, -128])
  have hm := merge_left (literal (valuationOf q) (1803)) (literal (valuationOf q) (1810)) (countLit q [-121, -123]) (countLit q [-124, -127, -128]) (count1810 q) 1 (meaning1803 q) (meaning1810 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1810 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-121, -123]) + (countLit q [-124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1811)) (countLit q [-121, -123]) (countLit q [-124, -127, -128]) (count1810 q) 1 1 (meaning1803 q) (meaning1807 q) (meaning1811 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1807 = false ∨ valuation q 1811 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-121, -123]) + (countLit q [-124, -127, -128]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-124, -127, -128])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1812)) (countLit q [-121, -123]) (countLit q [-124, -127, -128]) (count1810 q) 1 2 (meaning1803 q) (meaning1808 q) (meaning1812 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1808 = false ∨ valuation q 1812 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E050.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112050
