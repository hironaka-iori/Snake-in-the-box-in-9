import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1799 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1785)) (literal (valuationOf q) (1794)) (literal (valuationOf q) (1799)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 1 2 (meaning1785 q) (meaning1794 q) (meaning1799 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1794 = false ∨ valuation q 1799 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1800 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1785)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1800)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 1 3 (meaning1785 q) (meaning1795 q) (meaning1800 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1795 = false ∨ valuation q 1800 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1801 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1785)) (literal (valuationOf q) (1796)) (literal (valuationOf q) (1801)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 1 4 (meaning1785 q) (meaning1796 q) (meaning1801 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1796 = false ∨ valuation q 1801 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_left (literal (valuationOf q) (1786)) (literal (valuationOf q) (1798)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 2 (meaning1786 q) (meaning1798 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1798 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1799 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1786)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1799)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 2 1 (meaning1786 q) (meaning1793 q) (meaning1799 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1793 = false ∨ valuation q 1799 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1800 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1786)) (literal (valuationOf q) (1794)) (literal (valuationOf q) (1800)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 2 2 (meaning1786 q) (meaning1794 q) (meaning1800 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1794 = false ∨ valuation q 1800 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1801 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1786)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1801)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 2 3 (meaning1786 q) (meaning1795 q) (meaning1801 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1795 = false ∨ valuation q 1801 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1802 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1786)) (literal (valuationOf q) (1796)) (literal (valuationOf q) (1802)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 2 4 (meaning1786 q) (meaning1796 q) (meaning1802 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1796 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1796 = false ∨ valuation q 1802 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1799 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_left (literal (valuationOf q) (1787)) (literal (valuationOf q) (1799)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 3 (meaning1787 q) (meaning1799 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1799 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1800 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1800)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 3 1 (meaning1787 q) (meaning1793 q) (meaning1800 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1793 = false ∨ valuation q 1800 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1801 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1794)) (literal (valuationOf q) (1801)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 3 2 (meaning1787 q) (meaning1794 q) (meaning1801 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1794 = false ∨ valuation q 1801 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1802 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1802)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 3 3 (meaning1787 q) (meaning1795 q) (meaning1802 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1795 = false ∨ valuation q 1802 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1800 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_left (literal (valuationOf q) (1788)) (literal (valuationOf q) (1800)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 4 (meaning1788 q) (meaning1800 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1800 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1801 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1801)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 4 1 (meaning1788 q) (meaning1793 q) (meaning1801 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1793 = false ∨ valuation q 1801 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1802 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1794)) (literal (valuationOf q) (1802)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 4 2 (meaning1788 q) (meaning1794 q) (meaning1802 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1794 = false ∨ valuation q 1802 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1805)) (countLit q [-115]) (countLit q [-116]) (count1805 q) 1 (meaningNeg116 q) (meaning1805 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1805 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1805)) (countLit q [-115]) (countLit q [-116]) (count1805 q) 1 (meaningNeg115 q) (meaning1805 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1805 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1806 = true := by
  have hs : count1805 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1806)) (countLit q [-115]) (countLit q [-116]) (count1805 q) 1 1 (meaningNeg115 q) (meaningNeg116 q) (meaning1806 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 1806 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1807)) (countLit q [-118]) (countLit q [-120]) (count1807 q) 1 (meaningNeg120 q) (meaning1807 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1807 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-118)) (literal (valuationOf q) (1807)) (countLit q [-118]) (countLit q [-120]) (count1807 q) 1 (meaningNeg118 q) (meaning1807 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1807 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 120 = true ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_two (literal (valuationOf q) (-118)) (literal (valuationOf q) (-120)) (literal (valuationOf q) (1808)) (countLit q [-118]) (countLit q [-120]) (count1807 q) 1 1 (meaningNeg118 q) (meaningNeg120 q) (meaning1808 q) hs
  change (! (valuationOf q 118)) = false ∨ (! (valuationOf q 120)) = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 120 = true ∨ valuation q 1808 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 1807 = false ∨ valuationOf q 1809 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_right (literal (valuationOf q) (1807)) (literal (valuationOf q) (1809)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 1 (meaning1807 q) (meaning1809 q) hs
  change valuationOf q 1807 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 1807 = false ∨ valuation q 1809 = true := counterClause1750 (baseVal q)

theorem counterClause1751 (q : Nat → Bool) : valuationOf q 1808 = false ∨ valuationOf q 1810 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_right (literal (valuationOf q) (1808)) (literal (valuationOf q) (1810)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 2 (meaning1808 q) (meaning1810 q) hs
  change valuationOf q 1808 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 1808 = false ∨ valuation q 1810 = true := counterClause1751 (baseVal q)

theorem counterClause1752 (q : Nat → Bool) : valuationOf q 1805 = false ∨ valuationOf q 1809 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_left (literal (valuationOf q) (1805)) (literal (valuationOf q) (1809)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 1 (meaning1805 q) (meaning1809 q) hs
  change valuationOf q 1805 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 1805 = false ∨ valuation q 1809 = true := counterClause1752 (baseVal q)

theorem counterClause1753 (q : Nat → Bool) : valuationOf q 1805 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1810 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1805)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1810)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 1 1 (meaning1805 q) (meaning1807 q) (meaning1810 q) hs
  change valuationOf q 1805 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 1805 = false ∨ valuation q 1807 = false ∨ valuation q 1810 = true := counterClause1753 (baseVal q)

theorem counterClause1754 (q : Nat → Bool) : valuationOf q 1805 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1811 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1805)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1811)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 1 2 (meaning1805 q) (meaning1808 q) (meaning1811 q) hs
  change valuationOf q 1805 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 1805 = false ∨ valuation q 1808 = false ∨ valuation q 1811 = true := counterClause1754 (baseVal q)

theorem counterClause1755 (q : Nat → Bool) : valuationOf q 1806 = false ∨ valuationOf q 1810 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_left (literal (valuationOf q) (1806)) (literal (valuationOf q) (1810)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 2 (meaning1806 q) (meaning1810 q) hs
  change valuationOf q 1806 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 1806 = false ∨ valuation q 1810 = true := counterClause1755 (baseVal q)

theorem counterClause1756 (q : Nat → Bool) : valuationOf q 1806 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1806)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1811)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 2 1 (meaning1806 q) (meaning1807 q) (meaning1811 q) hs
  change valuationOf q 1806 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 1806 = false ∨ valuation q 1807 = false ∨ valuation q 1811 = true := counterClause1756 (baseVal q)

theorem counterClause1757 (q : Nat → Bool) : valuationOf q 1806 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true := by
  have hs : count1809 q = (countLit q [-115, -116]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1806)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1812)) (countLit q [-115, -116]) (countLit q [-118, -120]) (count1809 q) 2 2 (meaning1806 q) (meaning1808 q) (meaning1812 q) hs
  change valuationOf q 1806 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 1806 = false ∨ valuation q 1808 = false ∨ valuation q 1812 = true := counterClause1757 (baseVal q)

theorem counterClause1758 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1813 = true := by
  have hs : count1813 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1813)) (countLit q [-121]) (countLit q [-123]) (count1813 q) 1 (meaningNeg123 q) (meaning1813 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1813 = true := counterClause1758 (baseVal q)

theorem counterClause1759 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1813 = true := by
  have hs : count1813 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-121)) (literal (valuationOf q) (1813)) (countLit q [-121]) (countLit q [-123]) (count1813 q) 1 (meaningNeg121 q) (meaning1813 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1813 = true := counterClause1759 (baseVal q)

theorem counterClause1760 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1814 = true := by
  have hs : count1813 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-121)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1814)) (countLit q [-121]) (countLit q [-123]) (count1813 q) 1 1 (meaningNeg121 q) (meaningNeg123 q) (meaning1814 q) hs
  change (! (valuationOf q 121)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 123 = true ∨ valuation q 1814 = true := counterClause1760 (baseVal q)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E055.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112055
