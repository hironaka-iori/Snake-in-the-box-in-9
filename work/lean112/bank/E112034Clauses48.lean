import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1788)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 1 1 (meaning1775 q) (meaning1783 q) (meaning1788 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1783 = false ∨ valuation q 1788 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1789)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 1 2 (meaning1775 q) (meaning1784 q) (meaning1789 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1784 = false ∨ valuation q 1789 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1790)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 1 3 (meaning1775 q) (meaning1785 q) (meaning1790 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1785 = false ∨ valuation q 1790 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1791)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 1 4 (meaning1775 q) (meaning1786 q) (meaning1791 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1786 = false ∨ valuation q 1791 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1776)) (literal (valuationOf q) (1788)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 2 (meaning1776 q) (meaning1788 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1788 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1789)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 2 1 (meaning1776 q) (meaning1783 q) (meaning1789 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1783 = false ∨ valuation q 1789 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1790)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 2 2 (meaning1776 q) (meaning1784 q) (meaning1790 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1784 = false ∨ valuation q 1790 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1791)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 2 3 (meaning1776 q) (meaning1785 q) (meaning1791 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1785 = false ∨ valuation q 1791 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1792 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1792)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 2 4 (meaning1776 q) (meaning1786 q) (meaning1792 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1786 = false ∨ valuation q 1792 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1777)) (literal (valuationOf q) (1789)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 3 (meaning1777 q) (meaning1789 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1789 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1790)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 3 1 (meaning1777 q) (meaning1783 q) (meaning1790 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1783 = false ∨ valuation q 1790 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1791)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 3 2 (meaning1777 q) (meaning1784 q) (meaning1791 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1784 = false ∨ valuation q 1791 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1792 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1792)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 3 3 (meaning1777 q) (meaning1785 q) (meaning1792 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1785 = false ∨ valuation q 1792 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1793 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1793)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 3 4 (meaning1777 q) (meaning1786 q) (meaning1793 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1786 = false ∨ valuation q 1793 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1778)) (literal (valuationOf q) (1790)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 4 (meaning1778 q) (meaning1790 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1790 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1791)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 4 1 (meaning1778 q) (meaning1783 q) (meaning1791 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1783 = false ∨ valuation q 1791 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1792 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1792)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 4 2 (meaning1778 q) (meaning1784 q) (meaning1792 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1784 = false ∨ valuation q 1792 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1795)) (countLit q [-112]) (countLit q [-113]) (count1795 q) 1 (meaningNeg113 q) (meaning1795 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1795 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1795)) (countLit q [-112]) (countLit q [-113]) (count1795 q) 1 (meaningNeg112 q) (meaning1795 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1795 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1796 = true := by
  have hs : count1795 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1796)) (countLit q [-112]) (countLit q [-113]) (count1795 q) 1 1 (meaningNeg112 q) (meaningNeg113 q) (meaning1796 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1796 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 1796 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1797)) (countLit q [-117]) (countLit q [-118]) (count1797 q) 1 (meaningNeg118 q) (meaning1797 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1797 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-117)) (literal (valuationOf q) (1797)) (countLit q [-117]) (countLit q [-118]) (count1797 q) 1 (meaningNeg117 q) (meaning1797 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1797 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-117)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1798)) (countLit q [-117]) (countLit q [-118]) (count1797 q) 1 1 (meaningNeg117 q) (meaningNeg118 q) (meaning1798 q) hs
  change (! (valuationOf q 117)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 1798 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_right (literal (valuationOf q) (1797)) (literal (valuationOf q) (1799)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 1 (meaning1797 q) (meaning1799 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1799 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_right (literal (valuationOf q) (1798)) (literal (valuationOf q) (1800)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 2 (meaning1798 q) (meaning1800 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1800 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_left (literal (valuationOf q) (1795)) (literal (valuationOf q) (1799)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 1 (meaning1795 q) (meaning1799 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1799 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_two (literal (valuationOf q) (1795)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1800)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 1 1 (meaning1795 q) (meaning1797 q) (meaning1800 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1797 = false ∨ valuation q 1800 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_two (literal (valuationOf q) (1795)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1801)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 1 2 (meaning1795 q) (meaning1798 q) (meaning1801 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1798 = false ∨ valuation q 1801 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_left (literal (valuationOf q) (1796)) (literal (valuationOf q) (1800)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 2 (meaning1796 q) (meaning1800 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1800 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_two (literal (valuationOf q) (1796)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1801)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 2 1 (meaning1796 q) (meaning1797 q) (meaning1801 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1797 = false ∨ valuation q 1801 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-112, -113]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-117, -118])
  have hm := merge_two (literal (valuationOf q) (1796)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1802)) (countLit q [-112, -113]) (countLit q [-117, -118]) (count1799 q) 2 2 (meaning1796 q) (meaning1798 q) (meaning1802 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1798 = false ∨ valuation q 1802 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1803 = true := by
  have hs : count1803 q = (countLit q [-120]) + (countLit q [-121]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-121])
  have hm := merge_right (literal (valuationOf q) (-121)) (literal (valuationOf q) (1803)) (countLit q [-120]) (countLit q [-121]) (count1803 q) 1 (meaningNeg121 q) (meaning1803 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1803 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E034.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112034
