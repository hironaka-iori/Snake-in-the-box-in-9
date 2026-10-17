import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1793 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1729)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 3 2 (meaning1715 q) (meaning1722 q) (meaning1729 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1722 = false ∨ valuation q 1729 = true := counterClause1793 (baseVal q)

theorem counterClause1794 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_left (literal (valuationOf q) (1716)) (literal (valuationOf q) (1728)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 4 (meaning1716 q) (meaning1728 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1728 = true := counterClause1794 (baseVal q)

theorem counterClause1795 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1729)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 4 1 (meaning1716 q) (meaning1721 q) (meaning1729 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1721 = false ∨ valuation q 1729 = true := counterClause1795 (baseVal q)

theorem counterClause1796 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1730 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1730)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 4 2 (meaning1716 q) (meaning1722 q) (meaning1730 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1722 = false ∨ valuation q 1730 = true := counterClause1796 (baseVal q)

theorem counterClause1797 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1733)) (countLit q [-111]) (countLit q [-113]) (count1733 q) 1 (meaningNeg113 q) (meaning1733 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1733 = true := counterClause1797 (baseVal q)

theorem counterClause1798 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1733)) (countLit q [-111]) (countLit q [-113]) (count1733 q) 1 (meaningNeg111 q) (meaning1733 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1733 = true := counterClause1798 (baseVal q)

theorem counterClause1799 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1734)) (countLit q [-111]) (countLit q [-113]) (count1733 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1734 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1734 = true := counterClause1799 (baseVal q)

theorem counterClause1800 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1735)) (countLit q [-115]) (countLit q [-117]) (count1735 q) 1 (meaningNeg117 q) (meaning1735 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1735 = true := counterClause1800 (baseVal q)

theorem counterClause1801 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1735)) (countLit q [-115]) (countLit q [-117]) (count1735 q) 1 (meaningNeg115 q) (meaning1735 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1735 = true := counterClause1801 (baseVal q)

theorem counterClause1802 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1736)) (countLit q [-115]) (countLit q [-117]) (count1735 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1736 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1736 = true := counterClause1802 (baseVal q)

theorem counterClause1803 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1735)) (literal (valuationOf q) (1737)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 1 (meaning1735 q) (meaning1737 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1737 = true := counterClause1803 (baseVal q)

theorem counterClause1804 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1736)) (literal (valuationOf q) (1738)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 2 (meaning1736 q) (meaning1738 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1738 = true := counterClause1804 (baseVal q)

theorem counterClause1805 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1733)) (literal (valuationOf q) (1737)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 1 (meaning1733 q) (meaning1737 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1737 = true := counterClause1805 (baseVal q)

theorem counterClause1806 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1738)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 1 1 (meaning1733 q) (meaning1735 q) (meaning1738 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1735 = false ∨ valuation q 1738 = true := counterClause1806 (baseVal q)

theorem counterClause1807 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1739 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1739)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 1 2 (meaning1733 q) (meaning1736 q) (meaning1739 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1736 = false ∨ valuation q 1739 = true := counterClause1807 (baseVal q)

theorem counterClause1808 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1734)) (literal (valuationOf q) (1738)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 2 (meaning1734 q) (meaning1738 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1738 = true := counterClause1808 (baseVal q)

theorem counterClause1809 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1739 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1739)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 2 1 (meaning1734 q) (meaning1735 q) (meaning1739 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1735 = false ∨ valuation q 1739 = true := counterClause1809 (baseVal q)

theorem counterClause1810 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1740 = true := by
  have hs : count1737 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1740)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1737 q) 2 2 (meaning1734 q) (meaning1736 q) (meaning1740 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1736 = false ∨ valuation q 1740 = true := counterClause1810 (baseVal q)

theorem counterClause1811 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1741)) (countLit q [-119]) (countLit q [-120]) (count1741 q) 1 (meaningNeg120 q) (meaning1741 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1741 = true := counterClause1811 (baseVal q)

theorem counterClause1812 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-119)) (literal (valuationOf q) (1741)) (countLit q [-119]) (countLit q [-120]) (count1741 q) 1 (meaningNeg119 q) (meaning1741 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1741 = true := counterClause1812 (baseVal q)

theorem counterClause1813 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 120 = true ∨ valuationOf q 1742 = true := by
  have hs : count1741 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_two (literal (valuationOf q) (-119)) (literal (valuationOf q) (-120)) (literal (valuationOf q) (1742)) (countLit q [-119]) (countLit q [-120]) (count1741 q) 1 1 (meaningNeg119 q) (meaningNeg120 q) (meaning1742 q) hs
  change (! (valuationOf q 119)) = false ∨ (! (valuationOf q 120)) = false ∨ valuationOf q 1742 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 1742 = true := counterClause1813 (baseVal q)

theorem counterClause1814 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1743)) (countLit q [-122]) (countLit q [-123]) (count1743 q) 1 (meaningNeg123 q) (meaning1743 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1743 = true := counterClause1814 (baseVal q)

theorem counterClause1815 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-122)) (literal (valuationOf q) (1743)) (countLit q [-122]) (countLit q [-123]) (count1743 q) 1 (meaningNeg122 q) (meaning1743 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1743 = true := counterClause1815 (baseVal q)

theorem counterClause1816 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-122)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1744)) (countLit q [-122]) (countLit q [-123]) (count1743 q) 1 1 (meaningNeg122 q) (meaningNeg123 q) (meaning1744 q) hs
  change (! (valuationOf q 122)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1816 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 1744 = true := counterClause1816 (baseVal q)

theorem counterClause1817 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -123])
  have hm := merge_right (literal (valuationOf q) (1743)) (literal (valuationOf q) (1745)) (countLit q [-119, -120]) (countLit q [-122, -123]) (count1745 q) 1 (meaning1743 q) (meaning1745 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1817 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1745 = true := counterClause1817 (baseVal q)

theorem counterClause1818 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -123])
  have hm := merge_right (literal (valuationOf q) (1744)) (literal (valuationOf q) (1746)) (countLit q [-119, -120]) (countLit q [-122, -123]) (count1745 q) 2 (meaning1744 q) (meaning1746 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1818 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1746 = true := counterClause1818 (baseVal q)

theorem counterClause1819 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -123])
  have hm := merge_left (literal (valuationOf q) (1741)) (literal (valuationOf q) (1745)) (countLit q [-119, -120]) (countLit q [-122, -123]) (count1745 q) 1 (meaning1741 q) (meaning1745 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1819 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1745 = true := counterClause1819 (baseVal q)

theorem counterClause1820 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1746)) (countLit q [-119, -120]) (countLit q [-122, -123]) (count1745 q) 1 1 (meaning1741 q) (meaning1743 q) (meaning1746 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1820 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1743 = false ∨ valuation q 1746 = true := counterClause1820 (baseVal q)

theorem counterClause1821 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1747 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1747)) (countLit q [-119, -120]) (countLit q [-122, -123]) (count1745 q) 1 2 (meaning1741 q) (meaning1744 q) (meaning1747 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1821 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1744 = false ∨ valuation q 1747 = true := counterClause1821 (baseVal q)

theorem counterClause1822 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -123])
  have hm := merge_left (literal (valuationOf q) (1742)) (literal (valuationOf q) (1746)) (countLit q [-119, -120]) (countLit q [-122, -123]) (count1745 q) 2 (meaning1742 q) (meaning1746 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1822 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1746 = true := counterClause1822 (baseVal q)

theorem counterClause1823 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1747 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1747)) (countLit q [-119, -120]) (countLit q [-122, -123]) (count1745 q) 2 1 (meaning1742 q) (meaning1743 q) (meaning1747 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1823 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1743 = false ∨ valuation q 1747 = true := counterClause1823 (baseVal q)

theorem counterClause1824 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1749 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1745)) (literal (valuationOf q) (1749)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 1 (meaning1745 q) (meaning1749 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1824 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1749 = true := counterClause1824 (baseVal q)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E089.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h, clause1816 q h, clause1817 q h, clause1818 q h, clause1819 q h, clause1820 q h, clause1821 q h, clause1822 q h, clause1823 q h, clause1824 q h⟩

end
end Snake9.Regrowth.E112089
