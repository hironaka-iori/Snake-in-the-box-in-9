import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1771)) (countLit q [-95]) (countLit q [-97]) (count1771 q) 1 (meaningNeg95 q) (meaning1771 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1771 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1772 = true := by
  have hs : count1771 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1772)) (countLit q [-95]) (countLit q [-97]) (count1771 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1772 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1772 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1773 = true := by
  have hs : count1773 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1773)) (countLit q [-98]) (countLit q [-100]) (count1773 q) 1 (meaningNeg100 q) (meaning1773 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1773 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1773 = true := by
  have hs : count1773 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1773)) (countLit q [-98]) (countLit q [-100]) (count1773 q) 1 (meaningNeg98 q) (meaning1773 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1773 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1774 = true := by
  have hs : count1773 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1774)) (countLit q [-98]) (countLit q [-100]) (count1773 q) 1 1 (meaningNeg98 q) (meaningNeg100 q) (meaning1774 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 100 = true ∨ valuation q 1774 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1773)) (literal (valuationOf q) (1775)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 1 (meaning1773 q) (meaning1775 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1775 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1774)) (literal (valuationOf q) (1776)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 2 (meaning1774 q) (meaning1776 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1776 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (1771)) (literal (valuationOf q) (1775)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 1 (meaning1771 q) (meaning1775 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1775 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1776)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 1 1 (meaning1771 q) (meaning1773 q) (meaning1776 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1773 = false ∨ valuation q 1776 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1777)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 1 2 (meaning1771 q) (meaning1774 q) (meaning1777 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1774 = false ∨ valuation q 1777 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (1772)) (literal (valuationOf q) (1776)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 2 (meaning1772 q) (meaning1776 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1776 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1777)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 2 1 (meaning1772 q) (meaning1773 q) (meaning1777 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1773 = false ∨ valuation q 1777 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-95, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1778)) (countLit q [-95, -97]) (countLit q [-98, -100]) (count1775 q) 2 2 (meaning1772 q) (meaning1774 q) (meaning1778 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1774 = false ∨ valuation q 1778 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1779)) (countLit q [-103]) (countLit q [-104]) (count1779 q) 1 (meaningNeg104 q) (meaning1779 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1779 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1779)) (countLit q [-103]) (countLit q [-104]) (count1779 q) 1 (meaningNeg103 q) (meaning1779 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1779 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1780 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1780)) (countLit q [-103]) (countLit q [-104]) (count1779 q) 1 1 (meaningNeg103 q) (meaningNeg104 q) (meaning1780 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 1780 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1781)) (countLit q [-107]) (countLit q [-109]) (count1781 q) 1 (meaningNeg109 q) (meaning1781 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1781 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1781)) (countLit q [-107]) (countLit q [-109]) (count1781 q) 1 (meaningNeg107 q) (meaning1781 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1781 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1782 = true := by
  have hs : count1781 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1782)) (countLit q [-107]) (countLit q [-109]) (count1781 q) 1 1 (meaningNeg107 q) (meaningNeg109 q) (meaning1782 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 1782 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1781)) (literal (valuationOf q) (1783)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 1 (meaning1781 q) (meaning1783 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1783 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1782 = false ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1782)) (literal (valuationOf q) (1784)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 2 (meaning1782 q) (meaning1784 q) hs
  change valuationOf q 1782 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1782 = false ∨ valuation q 1784 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1779)) (literal (valuationOf q) (1783)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 1 (meaning1779 q) (meaning1783 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1783 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1784)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 1 1 (meaning1779 q) (meaning1781 q) (meaning1784 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1781 = false ∨ valuation q 1784 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1785 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1779)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1785)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 1 2 (meaning1779 q) (meaning1782 q) (meaning1785 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1782 = false ∨ valuation q 1785 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1780)) (literal (valuationOf q) (1784)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 2 (meaning1780 q) (meaning1784 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1784 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1785 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1785)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 2 1 (meaning1780 q) (meaning1781 q) (meaning1785 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1781 = false ∨ valuation q 1785 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1786 = true := by
  have hs : count1783 q = (countLit q [-103, -104]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1786)) (countLit q [-103, -104]) (countLit q [-107, -109]) (count1783 q) 2 2 (meaning1780 q) (meaning1782 q) (meaning1786 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1782 = false ∨ valuation q 1786 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1783 = false ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1783)) (literal (valuationOf q) (1787)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 1 (meaning1783 q) (meaning1787 q) hs
  change valuationOf q 1783 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1783 = false ∨ valuation q 1787 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1784 = false ∨ valuationOf q 1788 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1784)) (literal (valuationOf q) (1788)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 2 (meaning1784 q) (meaning1788 q) hs
  change valuationOf q 1784 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1784 = false ∨ valuation q 1788 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1789 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1785)) (literal (valuationOf q) (1789)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 3 (meaning1785 q) (meaning1789 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1789 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1790 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1786)) (literal (valuationOf q) (1790)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 4 (meaning1786 q) (meaning1790 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1790 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1775 = false ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-95, -97, -98, -100]) + (countLit q [-103, -104, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100]) (l₂ := [-103, -104, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1775)) (literal (valuationOf q) (1787)) (countLit q [-95, -97, -98, -100]) (countLit q [-103, -104, -107, -109]) (count1787 q) 1 (meaning1775 q) (meaning1787 q) hs
  change valuationOf q 1775 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1775 = false ∨ valuation q 1787 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E034.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112034
