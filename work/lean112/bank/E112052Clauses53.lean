import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1765 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1765)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 2 1 (meaning1760 q) (meaning1761 q) (meaning1765 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1761 = false ∨ valuation q 1765 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1760 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1766 = true := by
  have hs : count1763 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_two (literal (valuationOf q) (1760)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1766)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count1763 q) 2 2 (meaning1760 q) (meaning1762 q) (meaning1766 q) hs
  change valuationOf q 1760 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1760 = false ∨ valuation q 1762 = false ∨ valuation q 1766 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1767 = true := by
  have hs : count1767 q = (countLit q [-103]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1767)) (countLit q [-103]) (countLit q [-107]) (count1767 q) 1 (meaningNeg107 q) (meaning1767 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1767 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1767 = true := by
  have hs : count1767 q = (countLit q [-103]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1767)) (countLit q [-103]) (countLit q [-107]) (count1767 q) 1 (meaningNeg103 q) (meaning1767 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1767 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1768 = true := by
  have hs : count1767 q = (countLit q [-103]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1768)) (countLit q [-103]) (countLit q [-107]) (count1767 q) 1 1 (meaningNeg103 q) (meaningNeg107 q) (meaning1768 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 107 = true ∨ valuation q 1768 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1769 = true := by
  have hs : count1769 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1769)) (countLit q [-108]) (countLit q [-110]) (count1769 q) 1 (meaningNeg110 q) (meaning1769 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1769 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1769 = true := by
  have hs : count1769 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (1769)) (countLit q [-108]) (countLit q [-110]) (count1769 q) 1 (meaningNeg108 q) (meaning1769 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1769 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1770 = true := by
  have hs : count1769 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-108)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1770)) (countLit q [-108]) (countLit q [-110]) (count1769 q) 1 1 (meaningNeg108 q) (meaningNeg110 q) (meaning1770 q) hs
  change (! (valuationOf q 108)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 1770 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_right (literal (valuationOf q) (1769)) (literal (valuationOf q) (1771)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 1 (meaning1769 q) (meaning1771 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1771 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1772 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_right (literal (valuationOf q) (1770)) (literal (valuationOf q) (1772)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 2 (meaning1770 q) (meaning1772 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1772 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1767 = false ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_left (literal (valuationOf q) (1767)) (literal (valuationOf q) (1771)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 1 (meaning1767 q) (meaning1771 q) hs
  change valuationOf q 1767 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1767 = false ∨ valuation q 1771 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1767 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1772 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_two (literal (valuationOf q) (1767)) (literal (valuationOf q) (1769)) (literal (valuationOf q) (1772)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 1 1 (meaning1767 q) (meaning1769 q) (meaning1772 q) hs
  change valuationOf q 1767 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1767 = false ∨ valuation q 1769 = false ∨ valuation q 1772 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1767 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1773 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_two (literal (valuationOf q) (1767)) (literal (valuationOf q) (1770)) (literal (valuationOf q) (1773)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 1 2 (meaning1767 q) (meaning1770 q) (meaning1773 q) hs
  change valuationOf q 1767 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1767 = false ∨ valuation q 1770 = false ∨ valuation q 1773 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1772 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_left (literal (valuationOf q) (1768)) (literal (valuationOf q) (1772)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 2 (meaning1768 q) (meaning1772 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1772 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1773 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_two (literal (valuationOf q) (1768)) (literal (valuationOf q) (1769)) (literal (valuationOf q) (1773)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 2 1 (meaning1768 q) (meaning1769 q) (meaning1773 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1769 = false ∨ valuation q 1773 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1774 = true := by
  have hs : count1771 q = (countLit q [-103, -107]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -107]) (l₂ := [-108, -110])
  have hm := merge_two (literal (valuationOf q) (1768)) (literal (valuationOf q) (1770)) (literal (valuationOf q) (1774)) (countLit q [-103, -107]) (countLit q [-108, -110]) (count1771 q) 2 2 (meaning1768 q) (meaning1770 q) (meaning1774 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1770 = false ∨ valuation q 1774 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_right (literal (valuationOf q) (1771)) (literal (valuationOf q) (1775)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 1 (meaning1771 q) (meaning1775 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1775 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_right (literal (valuationOf q) (1772)) (literal (valuationOf q) (1776)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 2 (meaning1772 q) (meaning1776 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1776 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_right (literal (valuationOf q) (1773)) (literal (valuationOf q) (1777)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 3 (meaning1773 q) (meaning1777 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1777 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_right (literal (valuationOf q) (1774)) (literal (valuationOf q) (1778)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 4 (meaning1774 q) (meaning1778 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1778 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_left (literal (valuationOf q) (1763)) (literal (valuationOf q) (1775)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 1 (meaning1763 q) (meaning1775 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1775 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1771)) (literal (valuationOf q) (1776)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 1 1 (meaning1763 q) (meaning1771 q) (meaning1776 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1771 = false ∨ valuation q 1776 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1772)) (literal (valuationOf q) (1777)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 1 2 (meaning1763 q) (meaning1772 q) (meaning1777 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1772 = false ∨ valuation q 1777 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1778)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 1 3 (meaning1763 q) (meaning1773 q) (meaning1778 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1773 = false ∨ valuation q 1778 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1779 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1763)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1779)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 1 4 (meaning1763 q) (meaning1774 q) (meaning1779 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1774 = false ∨ valuation q 1779 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_left (literal (valuationOf q) (1764)) (literal (valuationOf q) (1776)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 2 (meaning1764 q) (meaning1776 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1776 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1771)) (literal (valuationOf q) (1777)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 2 1 (meaning1764 q) (meaning1771 q) (meaning1777 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1771 = false ∨ valuation q 1777 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1772)) (literal (valuationOf q) (1778)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 2 2 (meaning1764 q) (meaning1772 q) (meaning1778 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1772 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1772 = false ∨ valuation q 1778 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1779 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1779)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 2 3 (meaning1764 q) (meaning1773 q) (meaning1779 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1773 = false ∨ valuation q 1779 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1780 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1764)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1780)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 2 4 (meaning1764 q) (meaning1774 q) (meaning1780 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1774 = false ∨ valuation q 1780 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_left (literal (valuationOf q) (1765)) (literal (valuationOf q) (1777)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 3 (meaning1765 q) (meaning1777 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1777 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-96, -99, -100, -102]) + (countLit q [-103, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102]) (l₂ := [-103, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (1765)) (literal (valuationOf q) (1771)) (literal (valuationOf q) (1778)) (countLit q [-96, -99, -100, -102]) (countLit q [-103, -107, -108, -110]) (count1775 q) 3 1 (meaning1765 q) (meaning1771 q) (meaning1778 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1771 = false ∨ valuation q 1778 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E052.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112052
