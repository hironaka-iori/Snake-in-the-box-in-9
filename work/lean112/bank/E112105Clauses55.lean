import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1761 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1765 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1765)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 4 (meaning1729 q) (meaning1754 q) (meaning1765 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1754 = false ∨ valuation q 1765 = true := counterClause1761 (baseVal q)

theorem counterClause1762 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1766 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1766)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 5 (meaning1729 q) (meaning1755 q) (meaning1766 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1755 = false ∨ valuation q 1766 = true := counterClause1762 (baseVal q)

theorem counterClause1763 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1767 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1767)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 6 (meaning1729 q) (meaning1756 q) (meaning1767 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1756 = false ∨ valuation q 1767 = true := counterClause1763 (baseVal q)

theorem counterClause1764 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1768 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1768)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 7 (meaning1729 q) (meaning1757 q) (meaning1768 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1757 = false ∨ valuation q 1768 = true := counterClause1764 (baseVal q)

theorem counterClause1765 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1769 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1769)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 3 8 (meaning1729 q) (meaning1758 q) (meaning1769 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1758 = false ∨ valuation q 1769 = true := counterClause1765 (baseVal q)

theorem counterClause1766 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1763)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 1 (meaning1730 q) (meaning1751 q) (meaning1763 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1751 = false ∨ valuation q 1763 = true := counterClause1766 (baseVal q)

theorem counterClause1767 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1764 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1764)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 2 (meaning1730 q) (meaning1752 q) (meaning1764 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1752 = false ∨ valuation q 1764 = true := counterClause1767 (baseVal q)

theorem counterClause1768 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1765 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1765)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 3 (meaning1730 q) (meaning1753 q) (meaning1765 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1753 = false ∨ valuation q 1765 = true := counterClause1768 (baseVal q)

theorem counterClause1769 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1766 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1766)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 4 (meaning1730 q) (meaning1754 q) (meaning1766 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1754 = false ∨ valuation q 1766 = true := counterClause1769 (baseVal q)

theorem counterClause1770 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1767 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1767)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 5 (meaning1730 q) (meaning1755 q) (meaning1767 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1755 = false ∨ valuation q 1767 = true := counterClause1770 (baseVal q)

theorem counterClause1771 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1768 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1768)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 6 (meaning1730 q) (meaning1756 q) (meaning1768 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1756 = false ∨ valuation q 1768 = true := counterClause1771 (baseVal q)

theorem counterClause1772 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1769 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1769)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 7 (meaning1730 q) (meaning1757 q) (meaning1769 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1757 = false ∨ valuation q 1769 = true := counterClause1772 (baseVal q)

theorem counterClause1773 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1770 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1770)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 4 8 (meaning1730 q) (meaning1758 q) (meaning1770 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1758 = false ∨ valuation q 1770 = true := counterClause1773 (baseVal q)

theorem counterClause1774 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1764)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 1 (meaning1731 q) (meaning1751 q) (meaning1764 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1751 = false ∨ valuation q 1764 = true := counterClause1774 (baseVal q)

theorem counterClause1775 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1765 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1765)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 2 (meaning1731 q) (meaning1752 q) (meaning1765 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1752 = false ∨ valuation q 1765 = true := counterClause1775 (baseVal q)

theorem counterClause1776 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1766 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1766)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 3 (meaning1731 q) (meaning1753 q) (meaning1766 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1753 = false ∨ valuation q 1766 = true := counterClause1776 (baseVal q)

theorem counterClause1777 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1767 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1767)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 4 (meaning1731 q) (meaning1754 q) (meaning1767 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1754 = false ∨ valuation q 1767 = true := counterClause1777 (baseVal q)

theorem counterClause1778 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1768 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1768)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 5 (meaning1731 q) (meaning1755 q) (meaning1768 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1755 = false ∨ valuation q 1768 = true := counterClause1778 (baseVal q)

theorem counterClause1779 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1769 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1769)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 6 (meaning1731 q) (meaning1756 q) (meaning1769 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1756 = false ∨ valuation q 1769 = true := counterClause1779 (baseVal q)

theorem counterClause1780 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1770 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1770)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 7 (meaning1731 q) (meaning1757 q) (meaning1770 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1757 = false ∨ valuation q 1770 = true := counterClause1780 (baseVal q)

theorem counterClause1781 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1771 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1771)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 5 8 (meaning1731 q) (meaning1758 q) (meaning1771 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1758 = false ∨ valuation q 1771 = true := counterClause1781 (baseVal q)

theorem counterClause1782 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1764 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1732)) (literal (valuationOf q) (1764)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 (meaning1732 q) (meaning1764 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1764 = true := counterClause1782 (baseVal q)

theorem counterClause1783 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1765 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1765)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 1 (meaning1732 q) (meaning1751 q) (meaning1765 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1751 = false ∨ valuation q 1765 = true := counterClause1783 (baseVal q)

theorem counterClause1784 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1766 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1766)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 2 (meaning1732 q) (meaning1752 q) (meaning1766 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1752 = false ∨ valuation q 1766 = true := counterClause1784 (baseVal q)

theorem counterClause1785 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1767 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1767)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 3 (meaning1732 q) (meaning1753 q) (meaning1767 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1753 = false ∨ valuation q 1767 = true := counterClause1785 (baseVal q)

theorem counterClause1786 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1768 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1768)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 4 (meaning1732 q) (meaning1754 q) (meaning1768 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1754 = false ∨ valuation q 1768 = true := counterClause1786 (baseVal q)

theorem counterClause1787 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1769 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1769)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 5 (meaning1732 q) (meaning1755 q) (meaning1769 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1755 = false ∨ valuation q 1769 = true := counterClause1787 (baseVal q)

theorem counterClause1788 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1770 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1770)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 6 (meaning1732 q) (meaning1756 q) (meaning1770 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1756 = false ∨ valuation q 1770 = true := counterClause1788 (baseVal q)

theorem counterClause1789 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1771 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1771)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 7 (meaning1732 q) (meaning1757 q) (meaning1771 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1757 = false ∨ valuation q 1771 = true := counterClause1789 (baseVal q)

theorem counterClause1790 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1772 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1772)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 6 8 (meaning1732 q) (meaning1758 q) (meaning1772 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1758 = false ∨ valuation q 1772 = true := counterClause1790 (baseVal q)

theorem counterClause1791 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1766 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1766)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 7 1 (meaning1733 q) (meaning1751 q) (meaning1766 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1751 = false ∨ valuation q 1766 = true := counterClause1791 (baseVal q)

theorem counterClause1792 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1767 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1767)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 7 2 (meaning1733 q) (meaning1752 q) (meaning1767 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1752 = false ∨ valuation q 1767 = true := counterClause1792 (baseVal q)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E105.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112105
