import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1797)) (countLit q [-115]) (countLit q [-117]) (count1797 q) 1 (meaningNeg117 q) (meaning1797 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1797 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1797)) (countLit q [-115]) (countLit q [-117]) (count1797 q) 1 (meaningNeg115 q) (meaning1797 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1797 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1798)) (countLit q [-115]) (countLit q [-117]) (count1797 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1798 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1798 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1797 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1797)) (literal (valuationOf q) (1799)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 1 (meaning1797 q) (meaning1799 q) hs
  change valuationOf q 1797 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1797 = false ∨ valuation q 1799 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1798 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1798)) (literal (valuationOf q) (1800)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 2 (meaning1798 q) (meaning1800 q) hs
  change valuationOf q 1798 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false ∨ valuation q 1800 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1799 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1795)) (literal (valuationOf q) (1799)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 1 (meaning1795 q) (meaning1799 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1799 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1795)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1800)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 1 1 (meaning1795 q) (meaning1797 q) (meaning1800 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1797 = false ∨ valuation q 1800 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1795)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1801)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 1 2 (meaning1795 q) (meaning1798 q) (meaning1801 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1798 = false ∨ valuation q 1801 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1800 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1796)) (literal (valuationOf q) (1800)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 2 (meaning1796 q) (meaning1800 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1800 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1801 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1796)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1801)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 2 1 (meaning1796 q) (meaning1797 q) (meaning1801 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1797 = false ∨ valuation q 1801 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1802 = true := by
  have hs : count1799 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1796)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1802)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1799 q) 2 2 (meaning1796 q) (meaning1798 q) (meaning1802 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1798 = false ∨ valuation q 1802 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1803 = true := by
  have hs : count1803 q = (countLit q [-118]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-122])
  have hm := merge_right (literal (valuationOf q) (-122)) (literal (valuationOf q) (1803)) (countLit q [-118]) (countLit q [-122]) (count1803 q) 1 (meaningNeg122 q) (meaning1803 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1803 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1803 = true := by
  have hs : count1803 q = (countLit q [-118]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-122])
  have hm := merge_left (literal (valuationOf q) (-118)) (literal (valuationOf q) (1803)) (countLit q [-118]) (countLit q [-122]) (count1803 q) 1 (meaningNeg118 q) (meaning1803 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1803 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 122 = true ∨ valuationOf q 1804 = true := by
  have hs : count1803 q = (countLit q [-118]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-122])
  have hm := merge_two (literal (valuationOf q) (-118)) (literal (valuationOf q) (-122)) (literal (valuationOf q) (1804)) (countLit q [-118]) (countLit q [-122]) (count1803 q) 1 1 (meaningNeg118 q) (meaningNeg122 q) (meaning1804 q) hs
  change (! (valuationOf q 118)) = false ∨ (! (valuationOf q 122)) = false ∨ valuationOf q 1804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 122 = true ∨ valuation q 1804 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_right (literal (valuationOf q) (-126)) (literal (valuationOf q) (1805)) (countLit q [-125]) (countLit q [-126]) (count1805 q) 1 (meaningNeg126 q) (meaning1805 q) hs
  change (! (valuationOf q 126)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 1805 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 1805 = true := by
  have hs : count1805 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_left (literal (valuationOf q) (-125)) (literal (valuationOf q) (1805)) (countLit q [-125]) (countLit q [-126]) (count1805 q) 1 (meaningNeg125 q) (meaning1805 q) hs
  change (! (valuationOf q 125)) = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 1805 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 126 = true ∨ valuationOf q 1806 = true := by
  have hs : count1805 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_two (literal (valuationOf q) (-125)) (literal (valuationOf q) (-126)) (literal (valuationOf q) (1806)) (countLit q [-125]) (countLit q [-126]) (count1805 q) 1 1 (meaningNeg125 q) (meaningNeg126 q) (meaning1806 q) hs
  change (! (valuationOf q 125)) = false ∨ (! (valuationOf q 126)) = false ∨ valuationOf q 1806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 1806 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1805 = false ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-125, -126])
  have hm := merge_right (literal (valuationOf q) (1805)) (literal (valuationOf q) (1807)) (countLit q [-124]) (countLit q [-125, -126]) (count1807 q) 1 (meaning1805 q) (meaning1807 q) hs
  change valuationOf q 1805 = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1805 = false ∨ valuation q 1807 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1806 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-125, -126])
  have hm := merge_right (literal (valuationOf q) (1806)) (literal (valuationOf q) (1808)) (countLit q [-124]) (countLit q [-125, -126]) (count1807 q) 2 (meaning1806 q) (meaning1808 q) hs
  change valuationOf q 1806 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1806 = false ∨ valuation q 1808 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1807 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-125, -126])
  have hm := merge_left (literal (valuationOf q) (-124)) (literal (valuationOf q) (1807)) (countLit q [-124]) (countLit q [-125, -126]) (count1807 q) 1 (meaningNeg124 q) (meaning1807 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1807 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1805 = false ∨ valuationOf q 1808 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-125, -126])
  have hm := merge_two (literal (valuationOf q) (-124)) (literal (valuationOf q) (1805)) (literal (valuationOf q) (1808)) (countLit q [-124]) (countLit q [-125, -126]) (count1807 q) 1 1 (meaningNeg124 q) (meaning1805 q) (meaning1808 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1805 = false ∨ valuationOf q 1808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1805 = false ∨ valuation q 1808 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1806 = false ∨ valuationOf q 1809 = true := by
  have hs : count1807 q = (countLit q [-124]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-125, -126])
  have hm := merge_two (literal (valuationOf q) (-124)) (literal (valuationOf q) (1806)) (literal (valuationOf q) (1809)) (countLit q [-124]) (countLit q [-125, -126]) (count1807 q) 1 2 (meaningNeg124 q) (meaning1806 q) (meaning1809 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1806 = false ∨ valuationOf q 1809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1806 = false ∨ valuation q 1809 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1807 = false ∨ valuationOf q 1810 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1807)) (literal (valuationOf q) (1810)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 1 (meaning1807 q) (meaning1810 q) hs
  change valuationOf q 1807 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1807 = false ∨ valuation q 1810 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1808 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1808)) (literal (valuationOf q) (1811)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 2 (meaning1808 q) (meaning1811 q) hs
  change valuationOf q 1808 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1808 = false ∨ valuation q 1811 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1809 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1809)) (literal (valuationOf q) (1812)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 3 (meaning1809 q) (meaning1812 q) hs
  change valuationOf q 1809 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1809 = false ∨ valuation q 1812 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1810 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1803)) (literal (valuationOf q) (1810)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 1 (meaning1803 q) (meaning1810 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1810 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1811)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 1 1 (meaning1803 q) (meaning1807 q) (meaning1811 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1807 = false ∨ valuation q 1811 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1812)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 1 2 (meaning1803 q) (meaning1808 q) (meaning1812 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1808 = false ∨ valuation q 1812 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1803 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1813 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1803)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1813)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 1 3 (meaning1803 q) (meaning1809 q) (meaning1813 q) hs
  change valuationOf q 1803 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1803 = false ∨ valuation q 1809 = false ∨ valuation q 1813 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1804 = false ∨ valuationOf q 1811 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1804)) (literal (valuationOf q) (1811)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 2 (meaning1804 q) (meaning1811 q) hs
  change valuationOf q 1804 = false ∨ valuationOf q 1811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1804 = false ∨ valuation q 1811 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1804 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1812 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1804)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1812)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 2 1 (meaning1804 q) (meaning1807 q) (meaning1812 q) hs
  change valuationOf q 1804 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1804 = false ∨ valuation q 1807 = false ∨ valuation q 1812 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1804 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1813 = true := by
  have hs : count1810 q = (countLit q [-118, -122]) + (countLit q [-124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-118, -122]) (l₂ := [-124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1804)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1813)) (countLit q [-118, -122]) (countLit q [-124, -125, -126]) (count1810 q) 2 2 (meaning1804 q) (meaning1808 q) (meaning1813 q) hs
  change valuationOf q 1804 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1804 = false ∨ valuation q 1808 = false ∨ valuation q 1813 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E036.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112036
