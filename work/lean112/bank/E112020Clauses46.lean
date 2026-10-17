import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1753 = true := by
  have hs : count1747 q = (countLit q [-107, -109, -111, -113]) + (countLit q [-116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-107, -109, -111, -113]) (l₂ := [-116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1753)) (countLit q [-107, -109, -111, -113]) (countLit q [-116, -118, -121, -124]) (count1747 q) 4 3 (meaning1738 q) (meaning1745 q) (meaning1753 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1745 = false ∨ valuation q 1753 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1754 = true := by
  have hs : count1747 q = (countLit q [-107, -109, -111, -113]) + (countLit q [-116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-107, -109, -111, -113]) (l₂ := [-116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1754)) (countLit q [-107, -109, -111, -113]) (countLit q [-116, -118, -121, -124]) (count1747 q) 4 4 (meaning1738 q) (meaning1746 q) (meaning1754 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1746 = false ∨ valuation q 1754 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_right (literal (valuationOf q) (1750)) (literal (valuationOf q) (1758)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 4 (meaning1750 q) (meaning1758 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1758 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_right (literal (valuationOf q) (1751)) (literal (valuationOf q) (1759)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 5 (meaning1751 q) (meaning1759 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1759 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_right (literal (valuationOf q) (1752)) (literal (valuationOf q) (1760)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 6 (meaning1752 q) (meaning1760 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1760 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_right (literal (valuationOf q) (1753)) (literal (valuationOf q) (1761)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 7 (meaning1753 q) (meaning1761 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1761 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_right (literal (valuationOf q) (1754)) (literal (valuationOf q) (1762)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 8 (meaning1754 q) (meaning1762 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1762 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1758)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 1 3 (meaning1723 q) (meaning1749 q) (meaning1758 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1749 = false ∨ valuation q 1758 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1759)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 1 4 (meaning1723 q) (meaning1750 q) (meaning1759 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1750 = false ∨ valuation q 1759 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1760)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 1 5 (meaning1723 q) (meaning1751 q) (meaning1760 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1751 = false ∨ valuation q 1760 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1761)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 1 6 (meaning1723 q) (meaning1752 q) (meaning1761 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1752 = false ∨ valuation q 1761 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1762)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 1 7 (meaning1723 q) (meaning1753 q) (meaning1762 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1753 = false ∨ valuation q 1762 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1763)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 1 8 (meaning1723 q) (meaning1754 q) (meaning1763 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1754 = false ∨ valuation q 1763 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1758)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 2 2 (meaning1724 q) (meaning1748 q) (meaning1758 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1748 = false ∨ valuation q 1758 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1759)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 2 3 (meaning1724 q) (meaning1749 q) (meaning1759 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1749 = false ∨ valuation q 1759 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1760)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 2 4 (meaning1724 q) (meaning1750 q) (meaning1760 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1750 = false ∨ valuation q 1760 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1761)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 2 5 (meaning1724 q) (meaning1751 q) (meaning1761 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1751 = false ∨ valuation q 1761 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1762)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 2 6 (meaning1724 q) (meaning1752 q) (meaning1762 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1752 = false ∨ valuation q 1762 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1763)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 2 7 (meaning1724 q) (meaning1753 q) (meaning1763 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1753 = false ∨ valuation q 1763 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1758)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 3 1 (meaning1725 q) (meaning1747 q) (meaning1758 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1747 = false ∨ valuation q 1758 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1759)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 3 2 (meaning1725 q) (meaning1748 q) (meaning1759 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1748 = false ∨ valuation q 1759 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1760)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 3 3 (meaning1725 q) (meaning1749 q) (meaning1760 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1749 = false ∨ valuation q 1760 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1761)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 3 4 (meaning1725 q) (meaning1750 q) (meaning1761 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1750 = false ∨ valuation q 1761 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1762)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 3 5 (meaning1725 q) (meaning1751 q) (meaning1762 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1751 = false ∨ valuation q 1762 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1763)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 3 6 (meaning1725 q) (meaning1752 q) (meaning1763 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1752 = false ∨ valuation q 1763 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1759)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 4 1 (meaning1726 q) (meaning1747 q) (meaning1759 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1747 = false ∨ valuation q 1759 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1760)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 4 2 (meaning1726 q) (meaning1748 q) (meaning1760 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1748 = false ∨ valuation q 1760 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1761)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 4 3 (meaning1726 q) (meaning1749 q) (meaning1761 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1749 = false ∨ valuation q 1761 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1762)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 4 4 (meaning1726 q) (meaning1750 q) (meaning1762 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1750 = false ∨ valuation q 1762 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1763)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 4 5 (meaning1726 q) (meaning1751 q) (meaning1763 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1751 = false ∨ valuation q 1763 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_left (literal (valuationOf q) (1727)) (literal (valuationOf q) (1759)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 5 (meaning1727 q) (meaning1759 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1759 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) + (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96, -99, -100, -103, -104, -106]) (l₂ := [-107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1760)) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106]) (countLit q [-107, -109, -111, -113, -116, -118, -121, -124]) (count1755 q) 5 1 (meaning1727 q) (meaning1747 q) (meaning1760 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1747 = false ∨ valuation q 1760 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E020.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112020
