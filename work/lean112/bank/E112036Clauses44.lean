import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1784)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 1 1 (meaning1779 q) (meaning1781 q) (meaning1784 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1781 = false ∨ valuation q 1784 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1785 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1785)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 1 2 (meaning1779 q) (meaning1782 q) (meaning1785 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1782 = false ∨ valuation q 1785 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_left (literal (valuationOf q) (1780)) (literal (valuationOf q) (1784)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 2 (meaning1780 q) (meaning1784 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1784 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1785 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1785)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 2 1 (meaning1780 q) (meaning1781 q) (meaning1785 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1781 = false ∨ valuation q 1785 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1786 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1786)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 2 2 (meaning1780 q) (meaning1782 q) (meaning1786 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1782 = false ∨ valuation q 1786 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1783 = false ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_right (literal (valuationOf q) (1783)) (literal (valuationOf q) (1787)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 1 (meaning1783 q) (meaning1787 q) hs
  change valuationOf q 1783 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1783 = false ∨ valuation q 1787 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1784 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_right (literal (valuationOf q) (1784)) (literal (valuationOf q) (1788)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 2 (meaning1784 q) (meaning1788 q) hs
  change valuationOf q 1784 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1784 = false ∨ valuation q 1788 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_right (literal (valuationOf q) (1785)) (literal (valuationOf q) (1789)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 3 (meaning1785 q) (meaning1789 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1789 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_right (literal (valuationOf q) (1786)) (literal (valuationOf q) (1790)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 4 (meaning1786 q) (meaning1790 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1790 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_left (literal (valuationOf q) (1775)) (literal (valuationOf q) (1787)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 1 (meaning1775 q) (meaning1787 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1787 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1788)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 1 1 (meaning1775 q) (meaning1783 q) (meaning1788 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1783 = false ∨ valuation q 1788 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1789)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 1 2 (meaning1775 q) (meaning1784 q) (meaning1789 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1784 = false ∨ valuation q 1789 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1790)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 1 3 (meaning1775 q) (meaning1785 q) (meaning1790 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1785 = false ∨ valuation q 1790 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1775)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1791)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 1 4 (meaning1775 q) (meaning1786 q) (meaning1791 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1786 = false ∨ valuation q 1791 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_left (literal (valuationOf q) (1776)) (literal (valuationOf q) (1788)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 2 (meaning1776 q) (meaning1788 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1788 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1789)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 2 1 (meaning1776 q) (meaning1783 q) (meaning1789 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1783 = false ∨ valuation q 1789 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1790)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 2 2 (meaning1776 q) (meaning1784 q) (meaning1790 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1784 = false ∨ valuation q 1790 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1791)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 2 3 (meaning1776 q) (meaning1785 q) (meaning1791 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1785 = false ∨ valuation q 1791 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1776 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1792 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1776)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1792)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 2 4 (meaning1776 q) (meaning1786 q) (meaning1792 q) hs
  change valuationOf q 1776 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1776 = false ∨ valuation q 1786 = false ∨ valuation q 1792 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_left (literal (valuationOf q) (1777)) (literal (valuationOf q) (1789)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 3 (meaning1777 q) (meaning1789 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1789 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1790)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 3 1 (meaning1777 q) (meaning1783 q) (meaning1790 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1783 = false ∨ valuation q 1790 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1791)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 3 2 (meaning1777 q) (meaning1784 q) (meaning1791 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1784 = false ∨ valuation q 1791 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1792 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1792)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 3 3 (meaning1777 q) (meaning1785 q) (meaning1792 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1785 = false ∨ valuation q 1792 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1793 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1793)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 3 4 (meaning1777 q) (meaning1786 q) (meaning1793 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1786 = false ∨ valuation q 1793 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_left (literal (valuationOf q) (1778)) (literal (valuationOf q) (1790)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 4 (meaning1778 q) (meaning1790 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1790 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1791 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1791)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 4 1 (meaning1778 q) (meaning1783 q) (meaning1791 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1783 = false ∨ valuation q 1791 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1792 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1792)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 4 2 (meaning1778 q) (meaning1784 q) (meaning1792 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1784 = false ∨ valuation q 1792 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1793 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1793)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 4 3 (meaning1778 q) (meaning1785 q) (meaning1793 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1785 = false ∨ valuation q 1793 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1794 = true := by
  have hs : count1787 q = (countLit q [-96, -98, -100, -101]) + (countLit q [-103, -105, -106, -109]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101]) (l₂ := [-103, -105, -106, -109])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1794)) (countLit q [-96, -98, -100, -101]) (countLit q [-103, -105, -106, -109]) (count1787 q) 4 4 (meaning1778 q) (meaning1786 q) (meaning1794 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1786 = false ∨ valuation q 1794 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1795)) (countLit q [-112]) (countLit q [-114]) (count1795 q) 1 (meaningNeg114 q) (meaning1795 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1795 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1795)) (countLit q [-112]) (countLit q [-114]) (count1795 q) 1 (meaningNeg112 q) (meaning1795 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1795 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1796 = true := by
  have hs : count1795 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1796)) (countLit q [-112]) (countLit q [-114]) (count1795 q) 1 1 (meaningNeg112 q) (meaningNeg114 q) (meaning1796 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1796 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 1796 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E036.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112036
