import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1698 = true := by
  have hs : count1697 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1698)) (countLit q [-68]) (countLit q [-71]) (count1697 q) 1 1 (meaningNeg68 q) (meaningNeg71 q) (meaning1698 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 71 = true ∨ valuation q 1698 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_right (literal (valuationOf q) (1697)) (literal (valuationOf q) (1699)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 1 (meaning1697 q) (meaning1699 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1699 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_right (literal (valuationOf q) (1698)) (literal (valuationOf q) (1700)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 2 (meaning1698 q) (meaning1700 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1700 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_left (literal (valuationOf q) (1695)) (literal (valuationOf q) (1699)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 1 (meaning1695 q) (meaning1699 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1699 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1700)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 1 1 (meaning1695 q) (meaning1697 q) (meaning1700 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1697 = false ∨ valuation q 1700 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1701)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 1 2 (meaning1695 q) (meaning1698 q) (meaning1701 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1698 = false ∨ valuation q 1701 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_left (literal (valuationOf q) (1696)) (literal (valuationOf q) (1700)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 2 (meaning1696 q) (meaning1700 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1700 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1701)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 2 1 (meaning1696 q) (meaning1697 q) (meaning1701 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1697 = false ∨ valuation q 1701 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-65, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1702)) (countLit q [-65, -67]) (countLit q [-68, -71]) (count1699 q) 2 2 (meaning1696 q) (meaning1698 q) (meaning1702 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1698 = false ∨ valuation q 1702 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1703 = true := by
  have hs : count1703 q = (countLit q [-72]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1703)) (countLit q [-72]) (countLit q [-77]) (count1703 q) 1 (meaningNeg77 q) (meaning1703 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1703 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1703 = true := by
  have hs : count1703 q = (countLit q [-72]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1703)) (countLit q [-72]) (countLit q [-77]) (count1703 q) 1 (meaningNeg72 q) (meaning1703 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1703 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1704 = true := by
  have hs : count1703 q = (countLit q [-72]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1704)) (countLit q [-72]) (countLit q [-77]) (count1703 q) 1 1 (meaningNeg72 q) (meaningNeg77 q) (meaning1704 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 77 = true ∨ valuation q 1704 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1705 = true := by
  have hs : count1705 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1705)) (countLit q [-78]) (countLit q [-81]) (count1705 q) 1 (meaningNeg81 q) (meaning1705 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1705 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1705 = true := by
  have hs : count1705 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1705)) (countLit q [-78]) (countLit q [-81]) (count1705 q) 1 (meaningNeg78 q) (meaning1705 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1705 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1706 = true := by
  have hs : count1705 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1706)) (countLit q [-78]) (countLit q [-81]) (count1705 q) 1 1 (meaningNeg78 q) (meaningNeg81 q) (meaning1706 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 81 = true ∨ valuation q 1706 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_right (literal (valuationOf q) (1705)) (literal (valuationOf q) (1707)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 1 (meaning1705 q) (meaning1707 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1707 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1708 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_right (literal (valuationOf q) (1706)) (literal (valuationOf q) (1708)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 2 (meaning1706 q) (meaning1708 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1708 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_left (literal (valuationOf q) (1703)) (literal (valuationOf q) (1707)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 1 (meaning1703 q) (meaning1707 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1707 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1708 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1708)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 1 1 (meaning1703 q) (meaning1705 q) (meaning1708 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1705 = false ∨ valuation q 1708 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1709 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1709)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 1 2 (meaning1703 q) (meaning1706 q) (meaning1709 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1706 = false ∨ valuation q 1709 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1708 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_left (literal (valuationOf q) (1704)) (literal (valuationOf q) (1708)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 2 (meaning1704 q) (meaning1708 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1708 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1709 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1709)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 2 1 (meaning1704 q) (meaning1705 q) (meaning1709 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1705 = false ∨ valuation q 1709 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1710 = true := by
  have hs : count1707 q = (countLit q [-72, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -77]) (l₂ := [-78, -81])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1710)) (countLit q [-72, -77]) (countLit q [-78, -81]) (count1707 q) 2 2 (meaning1704 q) (meaning1706 q) (meaning1710 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1706 = false ∨ valuation q 1710 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1707)) (literal (valuationOf q) (1711)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 1 (meaning1707 q) (meaning1711 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1711 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1708)) (literal (valuationOf q) (1712)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 2 (meaning1708 q) (meaning1712 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1712 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1709)) (literal (valuationOf q) (1713)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 3 (meaning1709 q) (meaning1713 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1713 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1710)) (literal (valuationOf q) (1714)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 4 (meaning1710 q) (meaning1714 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1714 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1699)) (literal (valuationOf q) (1711)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 1 (meaning1699 q) (meaning1711 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1711 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1712)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 1 1 (meaning1699 q) (meaning1707 q) (meaning1712 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1707 = false ∨ valuation q 1712 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1713)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 1 2 (meaning1699 q) (meaning1708 q) (meaning1713 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1708 = false ∨ valuation q 1713 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1714)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 1 3 (meaning1699 q) (meaning1709 q) (meaning1714 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1709 = false ∨ valuation q 1714 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1715 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1715)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 1 4 (meaning1699 q) (meaning1710 q) (meaning1715 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1710 = false ∨ valuation q 1715 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E052.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112052
