import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1761 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_left (literal (valuationOf q) (1710)) (literal (valuationOf q) (1714)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 2 (meaning1710 q) (meaning1714 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1714 = true := counterClause1761 (baseVal q)

theorem counterClause1762 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1715 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1711)) (literal (valuationOf q) (1715)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 2 1 (meaning1710 q) (meaning1711 q) (meaning1715 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1711 = false ∨ valuation q 1715 = true := counterClause1762 (baseVal q)

theorem counterClause1763 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1716 = true := by
  have hs : count1713 q = (countLit q [-94, -96]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -99])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1716)) (countLit q [-94, -96]) (countLit q [-98, -99]) (count1713 q) 2 2 (meaning1710 q) (meaning1712 q) (meaning1716 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1712 = false ∨ valuation q 1716 = true := counterClause1763 (baseVal q)

theorem counterClause1764 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1717)) (countLit q [-102]) (countLit q [-103]) (count1717 q) 1 (meaningNeg103 q) (meaning1717 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1717 = true := counterClause1764 (baseVal q)

theorem counterClause1765 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1717)) (countLit q [-102]) (countLit q [-103]) (count1717 q) 1 (meaningNeg102 q) (meaning1717 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1717 = true := counterClause1765 (baseVal q)

theorem counterClause1766 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1718)) (countLit q [-102]) (countLit q [-103]) (count1717 q) 1 1 (meaningNeg102 q) (meaningNeg103 q) (meaning1718 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 1718 = true := counterClause1766 (baseVal q)

theorem counterClause1767 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1719)) (countLit q [-104]) (countLit q [-107]) (count1719 q) 1 (meaningNeg107 q) (meaning1719 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1719 = true := counterClause1767 (baseVal q)

theorem counterClause1768 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1719)) (countLit q [-104]) (countLit q [-107]) (count1719 q) 1 (meaningNeg104 q) (meaning1719 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1719 = true := counterClause1768 (baseVal q)

theorem counterClause1769 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1720)) (countLit q [-104]) (countLit q [-107]) (count1719 q) 1 1 (meaningNeg104 q) (meaningNeg107 q) (meaning1720 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 1720 = true := counterClause1769 (baseVal q)

theorem counterClause1770 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_right (literal (valuationOf q) (1719)) (literal (valuationOf q) (1721)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 1 (meaning1719 q) (meaning1721 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1721 = true := counterClause1770 (baseVal q)

theorem counterClause1771 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_right (literal (valuationOf q) (1720)) (literal (valuationOf q) (1722)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 2 (meaning1720 q) (meaning1722 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1722 = true := counterClause1771 (baseVal q)

theorem counterClause1772 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_left (literal (valuationOf q) (1717)) (literal (valuationOf q) (1721)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 1 (meaning1717 q) (meaning1721 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1721 = true := counterClause1772 (baseVal q)

theorem counterClause1773 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1722)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 1 1 (meaning1717 q) (meaning1719 q) (meaning1722 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = false ∨ valuation q 1722 = true := counterClause1773 (baseVal q)

theorem counterClause1774 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1723 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1723)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 1 2 (meaning1717 q) (meaning1720 q) (meaning1723 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1720 = false ∨ valuation q 1723 = true := counterClause1774 (baseVal q)

theorem counterClause1775 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_left (literal (valuationOf q) (1718)) (literal (valuationOf q) (1722)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 2 (meaning1718 q) (meaning1722 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1722 = true := counterClause1775 (baseVal q)

theorem counterClause1776 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1723 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1723)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 2 1 (meaning1718 q) (meaning1719 q) (meaning1723 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1719 = false ∨ valuation q 1723 = true := counterClause1776 (baseVal q)

theorem counterClause1777 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1724 = true := by
  have hs : count1721 q = (countLit q [-102, -103]) + (countLit q [-104, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -107])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1724)) (countLit q [-102, -103]) (countLit q [-104, -107]) (count1721 q) 2 2 (meaning1718 q) (meaning1720 q) (meaning1724 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1720 = false ∨ valuation q 1724 = true := counterClause1777 (baseVal q)

theorem counterClause1778 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_right (literal (valuationOf q) (1721)) (literal (valuationOf q) (1725)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 1 (meaning1721 q) (meaning1725 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1725 = true := counterClause1778 (baseVal q)

theorem counterClause1779 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_right (literal (valuationOf q) (1722)) (literal (valuationOf q) (1726)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 2 (meaning1722 q) (meaning1726 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1726 = true := counterClause1779 (baseVal q)

theorem counterClause1780 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_right (literal (valuationOf q) (1723)) (literal (valuationOf q) (1727)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 3 (meaning1723 q) (meaning1727 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1727 = true := counterClause1780 (baseVal q)

theorem counterClause1781 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_right (literal (valuationOf q) (1724)) (literal (valuationOf q) (1728)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 4 (meaning1724 q) (meaning1728 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1728 = true := counterClause1781 (baseVal q)

theorem counterClause1782 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_left (literal (valuationOf q) (1713)) (literal (valuationOf q) (1725)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 1 (meaning1713 q) (meaning1725 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1725 = true := counterClause1782 (baseVal q)

theorem counterClause1783 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1726)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 1 1 (meaning1713 q) (meaning1721 q) (meaning1726 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1721 = false ∨ valuation q 1726 = true := counterClause1783 (baseVal q)

theorem counterClause1784 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1727)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 1 2 (meaning1713 q) (meaning1722 q) (meaning1727 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1722 = false ∨ valuation q 1727 = true := counterClause1784 (baseVal q)

theorem counterClause1785 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1728)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 1 3 (meaning1713 q) (meaning1723 q) (meaning1728 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1723 = false ∨ valuation q 1728 = true := counterClause1785 (baseVal q)

theorem counterClause1786 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1729)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 1 4 (meaning1713 q) (meaning1724 q) (meaning1729 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1724 = false ∨ valuation q 1729 = true := counterClause1786 (baseVal q)

theorem counterClause1787 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_left (literal (valuationOf q) (1714)) (literal (valuationOf q) (1726)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 2 (meaning1714 q) (meaning1726 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1726 = true := counterClause1787 (baseVal q)

theorem counterClause1788 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1727)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 2 1 (meaning1714 q) (meaning1721 q) (meaning1727 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1721 = false ∨ valuation q 1727 = true := counterClause1788 (baseVal q)

theorem counterClause1789 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1728)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 2 2 (meaning1714 q) (meaning1722 q) (meaning1728 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1722 = false ∨ valuation q 1728 = true := counterClause1789 (baseVal q)

theorem counterClause1790 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1729)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 2 3 (meaning1714 q) (meaning1723 q) (meaning1729 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1723 = false ∨ valuation q 1729 = true := counterClause1790 (baseVal q)

theorem counterClause1791 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1727)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 3 (meaning1715 q) (meaning1727 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1727 = true := counterClause1791 (baseVal q)

theorem counterClause1792 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-94, -96, -98, -99]) + (countLit q [-102, -103, -104, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99]) (l₂ := [-102, -103, -104, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1728)) (countLit q [-94, -96, -98, -99]) (countLit q [-102, -103, -104, -107]) (count1725 q) 3 1 (meaning1715 q) (meaning1721 q) (meaning1728 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1721 = false ∨ valuation q 1728 = true := counterClause1792 (baseVal q)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E089.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112089
