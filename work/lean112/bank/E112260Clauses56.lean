import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1793 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1553)) (countLit q [-18]) (countLit q [-19]) (count1553 q) 1 (meaningNeg18 q) (meaning1553 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1553 = true := counterClause1793 (baseVal q)

theorem counterClause1794 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1554)) (countLit q [-18]) (countLit q [-19]) (count1553 q) 1 1 (meaningNeg18 q) (meaningNeg19 q) (meaning1554 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 1554 = true := counterClause1794 (baseVal q)

theorem counterClause1795 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1555)) (countLit q [-22]) (countLit q [-23]) (count1555 q) 1 (meaningNeg23 q) (meaning1555 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1555 = true := counterClause1795 (baseVal q)

theorem counterClause1796 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1555)) (countLit q [-22]) (countLit q [-23]) (count1555 q) 1 (meaningNeg22 q) (meaning1555 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1555 = true := counterClause1796 (baseVal q)

theorem counterClause1797 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1556)) (countLit q [-22]) (countLit q [-23]) (count1555 q) 1 1 (meaningNeg22 q) (meaningNeg23 q) (meaning1556 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 1556 = true := counterClause1797 (baseVal q)

theorem counterClause1798 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-18, -19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-18, -19]) (l₂ := [-22, -23])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1557)) (countLit q [-18, -19]) (countLit q [-22, -23]) (count1557 q) 1 (meaning1553 q) (meaning1557 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1557 = true := counterClause1798 (baseVal q)

theorem counterClause1799 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-18, -19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-18, -19]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1558)) (countLit q [-18, -19]) (countLit q [-22, -23]) (count1557 q) 1 1 (meaning1553 q) (meaning1555 q) (meaning1558 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1555 = false ∨ valuation q 1558 = true := counterClause1799 (baseVal q)

theorem counterClause1800 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-18, -19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-18, -19]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (countLit q [-18, -19]) (countLit q [-22, -23]) (count1557 q) 1 2 (meaning1553 q) (meaning1556 q) (meaning1559 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1556 = false ∨ valuation q 1559 = true := counterClause1800 (baseVal q)

theorem counterClause1801 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-18, -19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-18, -19]) (l₂ := [-22, -23])
  have hm := merge_left (literal (valuationOf q) (1554)) (literal (valuationOf q) (1558)) (countLit q [-18, -19]) (countLit q [-22, -23]) (count1557 q) 2 (meaning1554 q) (meaning1558 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1558 = true := counterClause1801 (baseVal q)

theorem counterClause1802 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-18, -19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-18, -19]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1559)) (countLit q [-18, -19]) (countLit q [-22, -23]) (count1557 q) 2 1 (meaning1554 q) (meaning1555 q) (meaning1559 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1555 = false ∨ valuation q 1559 = true := counterClause1802 (baseVal q)

theorem counterClause1803 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-18, -19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-18, -19]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-18, -19]) (countLit q [-22, -23]) (count1557 q) 2 2 (meaning1554 q) (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1803 (baseVal q)

theorem counterClause1804 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1561 = true := by
  have hs : count1561 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1561)) (countLit q [-25]) (countLit q [-27]) (count1561 q) 1 (meaningNeg27 q) (meaning1561 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1561 = true := counterClause1804 (baseVal q)

theorem counterClause1805 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1561 = true := by
  have hs : count1561 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1561)) (countLit q [-25]) (countLit q [-27]) (count1561 q) 1 (meaningNeg25 q) (meaning1561 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1561 = true := counterClause1805 (baseVal q)

theorem counterClause1806 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 27 = true ∨ valuationOf q 1562 = true := by
  have hs : count1561 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (1562)) (countLit q [-25]) (countLit q [-27]) (count1561 q) 1 1 (meaningNeg25 q) (meaningNeg27 q) (meaning1562 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 1562 = true := counterClause1806 (baseVal q)

theorem counterClause1807 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1563 = true := by
  have hs : count1563 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1563)) (countLit q [-29]) (countLit q [-31]) (count1563 q) 1 (meaningNeg31 q) (meaning1563 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1563 = true := counterClause1807 (baseVal q)

theorem counterClause1808 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1563 = true := by
  have hs : count1563 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1563)) (countLit q [-29]) (countLit q [-31]) (count1563 q) 1 (meaningNeg29 q) (meaning1563 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1563 = true := counterClause1808 (baseVal q)

theorem counterClause1809 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1564 = true := by
  have hs : count1563 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1564)) (countLit q [-29]) (countLit q [-31]) (count1563 q) 1 1 (meaningNeg29 q) (meaningNeg31 q) (meaning1564 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 1564 = true := counterClause1809 (baseVal q)

theorem counterClause1810 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1565 = true := by
  have hs : count1565 q = (countLit q [-25, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1563)) (literal (valuationOf q) (1565)) (countLit q [-25, -27]) (countLit q [-29, -31]) (count1565 q) 1 (meaning1563 q) (meaning1565 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1565 = true := counterClause1810 (baseVal q)

theorem counterClause1811 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1566 = true := by
  have hs : count1565 q = (countLit q [-25, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1564)) (literal (valuationOf q) (1566)) (countLit q [-25, -27]) (countLit q [-29, -31]) (count1565 q) 2 (meaning1564 q) (meaning1566 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1566 = true := counterClause1811 (baseVal q)

theorem counterClause1812 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1565 q = (countLit q [-25, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-25, -27]) (countLit q [-29, -31]) (count1565 q) 1 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1812 (baseVal q)

theorem counterClause1813 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1566 = true := by
  have hs : count1565 q = (countLit q [-25, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1566)) (countLit q [-25, -27]) (countLit q [-29, -31]) (count1565 q) 1 1 (meaning1561 q) (meaning1563 q) (meaning1566 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1563 = false ∨ valuation q 1566 = true := counterClause1813 (baseVal q)

theorem counterClause1814 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1567 = true := by
  have hs : count1565 q = (countLit q [-25, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1567)) (countLit q [-25, -27]) (countLit q [-29, -31]) (count1565 q) 1 2 (meaning1561 q) (meaning1564 q) (meaning1567 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1564 = false ∨ valuation q 1567 = true := counterClause1814 (baseVal q)

theorem counterClause1815 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1565 q = (countLit q [-25, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-25, -27]) (countLit q [-29, -31]) (count1565 q) 2 (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1566 = true := counterClause1815 (baseVal q)

theorem counterClause1816 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1567 = true := by
  have hs : count1565 q = (countLit q [-25, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1567)) (countLit q [-25, -27]) (countLit q [-29, -31]) (count1565 q) 2 1 (meaning1562 q) (meaning1563 q) (meaning1567 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1816 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1563 = false ∨ valuation q 1567 = true := counterClause1816 (baseVal q)

theorem counterClause1817 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1569)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 1 (meaning1557 q) (meaning1569 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1817 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1569 = true := counterClause1817 (baseVal q)

theorem counterClause1818 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1570)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 1 1 (meaning1557 q) (meaning1565 q) (meaning1570 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1818 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1565 = false ∨ valuation q 1570 = true := counterClause1818 (baseVal q)

theorem counterClause1819 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1571 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1571)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 1 2 (meaning1557 q) (meaning1566 q) (meaning1571 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1819 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1566 = false ∨ valuation q 1571 = true := counterClause1819 (baseVal q)

theorem counterClause1820 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1572 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1572)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 1 3 (meaning1557 q) (meaning1567 q) (meaning1572 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1820 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1567 = false ∨ valuation q 1572 = true := counterClause1820 (baseVal q)

theorem counterClause1821 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1570 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1558)) (literal (valuationOf q) (1570)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 2 (meaning1558 q) (meaning1570 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1821 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1570 = true := counterClause1821 (baseVal q)

theorem counterClause1822 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1571)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 2 1 (meaning1558 q) (meaning1565 q) (meaning1571 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1822 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1565 = false ∨ valuation q 1571 = true := counterClause1822 (baseVal q)

theorem counterClause1823 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1572 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1572)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 2 2 (meaning1558 q) (meaning1566 q) (meaning1572 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1823 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1566 = false ∨ valuation q 1572 = true := counterClause1823 (baseVal q)

theorem counterClause1824 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1571 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1559)) (literal (valuationOf q) (1571)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 3 (meaning1559 q) (meaning1571 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1824 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1571 = true := counterClause1824 (baseVal q)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E260.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h, clause1816 q h, clause1817 q h, clause1818 q h, clause1819 q h, clause1820 q h, clause1821 q h, clause1822 q h, clause1823 q h, clause1824 q h⟩

end
end Snake9.Regrowth.E112260
