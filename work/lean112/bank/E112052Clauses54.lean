import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1779 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1772)) (literal (valuationOf q) (1779)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 3 2 (meaning1765 q) (meaning1772 q) (meaning1779 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1772 = false ∨ valuation q 1779 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1780 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1780)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 3 3 (meaning1765 q) (meaning1773 q) (meaning1780 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1773 = false ∨ valuation q 1780 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1781 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1781)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 3 4 (meaning1765 q) (meaning1774 q) (meaning1781 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1774 = false ∨ valuation q 1781 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1766 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_left (literal (valuationOf q) (1766)) (literal (valuationOf q) (1778)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 4 (meaning1766 q) (meaning1778 q) hs
  change valuationOf q 1766 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1766 = false ∨ valuation q 1778 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1766 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1779 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1766)) (literal (valuationOf q) (1771)) (literal (valuationOf q) (1779)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 4 1 (meaning1766 q) (meaning1771 q) (meaning1779 q) hs
  change valuationOf q 1766 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1766 = false ∨ valuation q 1771 = false ∨ valuation q 1779 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1766 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1780 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1766)) (literal (valuationOf q) (1772)) (literal (valuationOf q) (1780)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 4 2 (meaning1766 q) (meaning1772 q) (meaning1780 q) hs
  change valuationOf q 1766 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1766 = false ∨ valuation q 1772 = false ∨ valuation q 1780 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1766 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1781 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1766)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1781)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 4 3 (meaning1766 q) (meaning1773 q) (meaning1781 q) hs
  change valuationOf q 1766 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1766 = false ∨ valuation q 1773 = false ∨ valuation q 1781 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1783)) (countLit q [-112]) (countLit q [-114]) (count1783 q) 1 (meaningNeg114 q) (meaning1783 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1783 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1783)) (countLit q [-112]) (countLit q [-114]) (count1783 q) 1 (meaningNeg112 q) (meaning1783 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1783 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1784)) (countLit q [-112]) (countLit q [-114]) (count1783 q) 1 1 (meaningNeg112 q) (meaningNeg114 q) (meaning1784 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 1784 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1785 = true := by
  have hs : count1785 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1785)) (countLit q [-118]) (countLit q [-120]) (count1785 q) 1 (meaningNeg120 q) (meaning1785 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1785 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1785 = true := by
  have hs : count1785 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-118)) (literal (valuationOf q) (1785)) (countLit q [-118]) (countLit q [-120]) (count1785 q) 1 (meaningNeg118 q) (meaning1785 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1785 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 120 = true ∨ valuationOf q 1786 = true := by
  have hs : count1785 q = (countLit q [-118]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-120])
  have hm := merge_two (literal (valuationOf q) (-118)) (literal (valuationOf q) (-120)) (literal (valuationOf q) (1786)) (countLit q [-118]) (countLit q [-120]) (count1785 q) 1 1 (meaningNeg118 q) (meaningNeg120 q) (meaning1786 q) hs
  change (! (valuationOf q 118)) = false ∨ (! (valuationOf q 120)) = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 120 = true ∨ valuation q 1786 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_right (literal (valuationOf q) (1785)) (literal (valuationOf q) (1787)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 1 (meaning1785 q) (meaning1787 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1787 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_right (literal (valuationOf q) (1786)) (literal (valuationOf q) (1788)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 2 (meaning1786 q) (meaning1788 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1788 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 1783 = false ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_left (literal (valuationOf q) (1783)) (literal (valuationOf q) (1787)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 1 (meaning1783 q) (meaning1787 q) hs
  change valuationOf q 1783 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 1783 = false ∨ valuation q 1787 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 1783 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1783)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1788)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 1 1 (meaning1783 q) (meaning1785 q) (meaning1788 q) hs
  change valuationOf q 1783 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 1783 = false ∨ valuation q 1785 = false ∨ valuation q 1788 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 1783 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1783)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1789)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 1 2 (meaning1783 q) (meaning1786 q) (meaning1789 q) hs
  change valuationOf q 1783 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 1783 = false ∨ valuation q 1786 = false ∨ valuation q 1789 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 1784 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_left (literal (valuationOf q) (1784)) (literal (valuationOf q) (1788)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 2 (meaning1784 q) (meaning1788 q) hs
  change valuationOf q 1784 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 1784 = false ∨ valuation q 1788 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 1784 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1784)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1789)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 2 1 (meaning1784 q) (meaning1785 q) (meaning1789 q) hs
  change valuationOf q 1784 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 1784 = false ∨ valuation q 1785 = false ∨ valuation q 1789 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 1784 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-112, -114]) + (countLit q [-118, -120]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -120])
  have hm := merge_two (literal (valuationOf q) (1784)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1790)) (countLit q [-112, -114]) (countLit q [-118, -120]) (count1787 q) 2 2 (meaning1784 q) (meaning1786 q) (meaning1790 q) hs
  change valuationOf q 1784 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 1784 = false ∨ valuation q 1786 = false ∨ valuation q 1790 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1791 = true := by
  have hs : count1791 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1791)) (countLit q [-122]) (countLit q [-123]) (count1791 q) 1 (meaningNeg123 q) (meaning1791 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1791 = true := counterClause1750 (baseVal q)

theorem counterClause1751 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1791 = true := by
  have hs : count1791 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-122)) (literal (valuationOf q) (1791)) (countLit q [-122]) (countLit q [-123]) (count1791 q) 1 (meaningNeg122 q) (meaning1791 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1791 = true := counterClause1751 (baseVal q)

theorem counterClause1752 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1792 = true := by
  have hs : count1791 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-122)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1792)) (countLit q [-122]) (countLit q [-123]) (count1791 q) 1 1 (meaningNeg122 q) (meaningNeg123 q) (meaning1792 q) hs
  change (! (valuationOf q 122)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 1792 = true := counterClause1752 (baseVal q)

theorem counterClause1753 (q : Nat → Bool) : valuationOf q 127 = true ∨ valuationOf q 1793 = true := by
  have hs : count1793 q = (countLit q [-126]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-126]) (l₂ := [-127])
  have hm := merge_right (literal (valuationOf q) (-127)) (literal (valuationOf q) (1793)) (countLit q [-126]) (countLit q [-127]) (count1793 q) 1 (meaningNeg127 q) (meaning1793 q) hs
  change (! (valuationOf q 127)) = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 127 = true ∨ valuation q 1793 = true := counterClause1753 (baseVal q)

theorem counterClause1754 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 1793 = true := by
  have hs : count1793 q = (countLit q [-126]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-126]) (l₂ := [-127])
  have hm := merge_left (literal (valuationOf q) (-126)) (literal (valuationOf q) (1793)) (countLit q [-126]) (countLit q [-127]) (count1793 q) 1 (meaningNeg126 q) (meaning1793 q) hs
  change (! (valuationOf q 126)) = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 1793 = true := counterClause1754 (baseVal q)

theorem counterClause1755 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 127 = true ∨ valuationOf q 1794 = true := by
  have hs : count1793 q = (countLit q [-126]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-126]) (l₂ := [-127])
  have hm := merge_two (literal (valuationOf q) (-126)) (literal (valuationOf q) (-127)) (literal (valuationOf q) (1794)) (countLit q [-126]) (countLit q [-127]) (count1793 q) 1 1 (meaningNeg126 q) (meaningNeg127 q) (meaning1794 q) hs
  change (! (valuationOf q 126)) = false ∨ (! (valuationOf q 127)) = false ∨ valuationOf q 1794 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 1794 = true := counterClause1755 (baseVal q)

theorem counterClause1756 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_right (literal (valuationOf q) (1793)) (literal (valuationOf q) (1795)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 1 (meaning1793 q) (meaning1795 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1795 = true := counterClause1756 (baseVal q)

theorem counterClause1757 (q : Nat → Bool) : valuationOf q 1794 = false ∨ valuationOf q 1796 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_right (literal (valuationOf q) (1794)) (literal (valuationOf q) (1796)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 2 (meaning1794 q) (meaning1796 q) hs
  change valuationOf q 1794 = false ∨ valuationOf q 1796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 1794 = false ∨ valuation q 1796 = true := counterClause1757 (baseVal q)

theorem counterClause1758 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_left (literal (valuationOf q) (1791)) (literal (valuationOf q) (1795)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 1 (meaning1791 q) (meaning1795 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1795 = true := counterClause1758 (baseVal q)

theorem counterClause1759 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1796 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1796)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 1 1 (meaning1791 q) (meaning1793 q) (meaning1796 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1793 = false ∨ valuation q 1796 = true := counterClause1759 (baseVal q)

theorem counterClause1760 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1797 = true := by
  have hs : count1795 q = (countLit q [-122, -123]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -123]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1794)) (literal (valuationOf q) (1797)) (countLit q [-122, -123]) (countLit q [-126, -127]) (count1795 q) 1 2 (meaning1791 q) (meaning1794 q) (meaning1797 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1794 = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1794 = false ∨ valuation q 1797 = true := counterClause1760 (baseVal q)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E052.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112052
