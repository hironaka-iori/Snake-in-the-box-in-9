import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1803 = true := by
  have hs : count1803 q = (countLit q [-120]) + (countLit q [-121]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-121])
  have hm := merge_left (literal (valuationOf q) (-120)) (literal (valuationOf q) (1803)) (countLit q [-120]) (countLit q [-121]) (count1803 q) 1 (meaningNeg120 q) (meaning1803 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1803 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 121 = true ∨ valuationOf q 1804 = true := by
  have hs : count1803 q = (countLit q [-120]) + (countLit q [-121]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-121])
  have hm := merge_two (literal (valuationOf q) (-120)) (literal (valuationOf q) (-121)) (literal (valuationOf q) (1804)) (countLit q [-120]) (countLit q [-121]) (count1803 q) 1 1 (meaningNeg120 q) (meaningNeg121 q) (meaning1804 q) hs
  change (! (valuationOf q 120)) = false ∨ (! (valuationOf q 121)) = false ∨ valuationOf q 1804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 1804 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_right (literal (valuationOf q) (-126)) (literal (valuationOf q) (1805)) (countLit q [-125]) (countLit q [-126]) (count1805 q) 1 (meaningNeg126 q) (meaning1805 q) hs
  change (! (valuationOf q 126)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 1805 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_left (literal (valuationOf q) (-125)) (literal (valuationOf q) (1805)) (countLit q [-125]) (countLit q [-126]) (count1805 q) 1 (meaningNeg125 q) (meaning1805 q) hs
  change (! (valuationOf q 125)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 1805 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 126 = true ∨ valuationOf q 1806 = true := by
  have hs : count1805 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_two (literal (valuationOf q) (-125)) (literal (valuationOf q) (-126)) (literal (valuationOf q) (1806)) (countLit q [-125]) (countLit q [-126]) (count1805 q) 1 1 (meaningNeg125 q) (meaningNeg126 q) (meaning1806 q) hs
  change (! (valuationOf q 125)) = false ∨ (! (valuationOf q 126)) = false ∨ valuationOf q 1806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 1806 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1805 = false ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-122]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-125, -126])
  have hm := merge_right (literal (valuationOf q) (1805)) (literal (valuationOf q) (1807)) (countLit q [-122]) (countLit q [-125, -126]) (count1807 q) 1 (meaning1805 q) (meaning1807 q) hs
  change valuationOf q 1805 = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1805 = false ∨ valuation q 1807 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1806 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-122]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-125, -126])
  have hm := merge_right (literal (valuationOf q) (1806)) (literal (valuationOf q) (1808)) (countLit q [-122]) (countLit q [-125, -126]) (count1807 q) 2 (meaning1806 q) (meaning1808 q) hs
  change valuationOf q 1806 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1806 = false ∨ valuation q 1808 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-122]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-125, -126])
  have hm := merge_left (literal (valuationOf q) (-122)) (literal (valuationOf q) (1807)) (countLit q [-122]) (countLit q [-125, -126]) (count1807 q) 1 (meaningNeg122 q) (meaning1807 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1807 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1805 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-122]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-125, -126])
  have hm := merge_two (literal (valuationOf q) (-122)) (literal (valuationOf q) (1805)) (literal (valuationOf q) (1808)) (countLit q [-122]) (countLit q [-125, -126]) (count1807 q) 1 1 (meaningNeg122 q) (meaning1805 q) (meaning1808 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1805 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1805 = false ∨ valuation q 1808 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1806 = false ∨ valuationOf q 1809 = true := by
  have hs : count1807 q = (countLit q [-122]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-125, -126])
  have hm := merge_two (literal (valuationOf q) (-122)) (literal (valuationOf q) (1806)) (literal (valuationOf q) (1809)) (countLit q [-122]) (countLit q [-125, -126]) (count1807 q) 1 2 (meaningNeg122 q) (meaning1806 q) (meaning1809 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1806 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1806 = false ∨ valuation q 1809 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1807 = false ∨ valuationOf q 1810 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1807)) (literal (valuationOf q) (1810)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 1 (meaning1807 q) (meaning1810 q) hs
  change valuationOf q 1807 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1807 = false ∨ valuation q 1810 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1808 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1808)) (literal (valuationOf q) (1811)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 2 (meaning1808 q) (meaning1811 q) hs
  change valuationOf q 1808 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1808 = false ∨ valuation q 1811 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1809)) (literal (valuationOf q) (1812)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 3 (meaning1809 q) (meaning1812 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1812 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1810 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1803)) (literal (valuationOf q) (1810)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 1 (meaning1803 q) (meaning1810 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1810 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1811)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 1 1 (meaning1803 q) (meaning1807 q) (meaning1811 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1807 = false ∨ valuation q 1811 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1812)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 1 2 (meaning1803 q) (meaning1808 q) (meaning1812 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1808 = false ∨ valuation q 1812 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1813 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1813)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 1 3 (meaning1803 q) (meaning1809 q) (meaning1813 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1809 = false ∨ valuation q 1813 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1804 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1804)) (literal (valuationOf q) (1811)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 2 (meaning1804 q) (meaning1811 q) hs
  change valuationOf q 1804 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1804 = false ∨ valuation q 1811 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1804 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1804)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1812)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 2 1 (meaning1804 q) (meaning1807 q) (meaning1812 q) hs
  change valuationOf q 1804 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1804 = false ∨ valuation q 1807 = false ∨ valuation q 1812 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1804 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1813 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1804)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1813)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 2 2 (meaning1804 q) (meaning1808 q) (meaning1813 q) hs
  change valuationOf q 1804 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1804 = false ∨ valuation q 1808 = false ∨ valuation q 1813 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1804 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1814 = true := by
  have hs : count1810 q = (countLit q [-120, -121]) + (countLit q [-122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -121]) (l₂ := [-122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1804)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1814)) (countLit q [-120, -121]) (countLit q [-122, -125, -126]) (count1810 q) 2 3 (meaning1804 q) (meaning1809 q) (meaning1814 q) hs
  change valuationOf q 1804 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1804 = false ∨ valuation q 1809 = false ∨ valuation q 1814 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1812 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1812)) (literal (valuationOf q) (1817)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 3 (meaning1812 q) (meaning1817 q) hs
  change valuationOf q 1812 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1812 = false ∨ valuation q 1817 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1813 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1813)) (literal (valuationOf q) (1818)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 4 (meaning1813 q) (meaning1818 q) hs
  change valuationOf q 1813 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1813 = false ∨ valuation q 1818 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1814 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1814)) (literal (valuationOf q) (1819)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 5 (meaning1814 q) (meaning1819 q) hs
  change valuationOf q 1814 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1814 = false ∨ valuation q 1819 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1815 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1799)) (literal (valuationOf q) (1815)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 1 (meaning1799 q) (meaning1815 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1815 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1816 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1816)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 1 1 (meaning1799 q) (meaning1810 q) (meaning1816 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1810 = false ∨ valuation q 1816 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1817)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 1 2 (meaning1799 q) (meaning1811 q) (meaning1817 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1811 = false ∨ valuation q 1817 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1818)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 1 3 (meaning1799 q) (meaning1812 q) (meaning1818 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1812 = false ∨ valuation q 1818 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1819)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 1 4 (meaning1799 q) (meaning1813 q) (meaning1819 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1813 = false ∨ valuation q 1819 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1820 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1820)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 1 5 (meaning1799 q) (meaning1814 q) (meaning1820 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1814 = false ∨ valuation q 1820 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1816 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1800)) (literal (valuationOf q) (1816)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 2 (meaning1800 q) (meaning1816 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1816 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1817)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 2 1 (meaning1800 q) (meaning1810 q) (meaning1817 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1810 = false ∨ valuation q 1817 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E034.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112034
