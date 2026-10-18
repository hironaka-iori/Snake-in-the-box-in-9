import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 1 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 2 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 3 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1591)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 1 (meaning1580 q) (meaning1591 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1591 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1592)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 1 1 (meaning1580 q) (meaning1587 q) (meaning1592 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1587 = false ∨ valuation q 1592 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1593)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 1 2 (meaning1580 q) (meaning1588 q) (meaning1593 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1588 = false ∨ valuation q 1593 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1594)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 1 3 (meaning1580 q) (meaning1589 q) (meaning1594 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1589 = false ∨ valuation q 1594 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1592)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 2 (meaning1581 q) (meaning1592 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1592 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1593)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 2 1 (meaning1581 q) (meaning1587 q) (meaning1593 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1587 = false ∨ valuation q 1593 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1594)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 2 2 (meaning1581 q) (meaning1588 q) (meaning1594 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1588 = false ∨ valuation q 1594 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-60, -65, -66]) + (countLit q [-68, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-68, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (countLit q [-60, -65, -66]) (countLit q [-68, -69, -70, -72]) (count1591 q) 3 (meaning1582 q) (meaning1593 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1593 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-75]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1598)) (countLit q [-75]) (countLit q [-78]) (count1598 q) 1 (meaningNeg78 q) (meaning1598 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1598 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-75]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1598)) (countLit q [-75]) (countLit q [-78]) (count1598 q) 1 (meaningNeg75 q) (meaning1598 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1598 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-75]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1599)) (countLit q [-75]) (countLit q [-78]) (count1598 q) 1 1 (meaningNeg75 q) (meaningNeg78 q) (meaning1599 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 78 = true ∨ valuation q 1599 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-74]) + (countLit q [-75, -78]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -78])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (countLit q [-74]) (countLit q [-75, -78]) (count1600 q) 1 (meaning1598 q) (meaning1600 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-74]) + (countLit q [-75, -78]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -78])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1601)) (countLit q [-74]) (countLit q [-75, -78]) (count1600 q) 2 (meaning1599 q) (meaning1601 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1601 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-74]) + (countLit q [-75, -78]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -78])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1600)) (countLit q [-74]) (countLit q [-75, -78]) (count1600 q) 1 (meaningNeg74 q) (meaning1600 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1600 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-74]) + (countLit q [-75, -78]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -78])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1601)) (countLit q [-74]) (countLit q [-75, -78]) (count1600 q) 1 1 (meaningNeg74 q) (meaning1598 q) (meaning1601 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1598 = false ∨ valuation q 1601 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true := by
  have hs : count1600 q = (countLit q [-74]) + (countLit q [-75, -78]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -78])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1602)) (countLit q [-74]) (countLit q [-75, -78]) (count1600 q) 1 2 (meaningNeg74 q) (meaning1599 q) (meaning1602 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1599 = false ∨ valuation q 1602 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-80]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1603)) (countLit q [-80]) (countLit q [-84]) (count1603 q) 1 (meaningNeg84 q) (meaning1603 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1603 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-80]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1603)) (countLit q [-80]) (countLit q [-84]) (count1603 q) 1 (meaningNeg80 q) (meaning1603 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1603 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1604 = true := by
  have hs : count1603 q = (countLit q [-80]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1604)) (countLit q [-80]) (countLit q [-84]) (count1603 q) 1 1 (meaningNeg80 q) (meaningNeg84 q) (meaning1604 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 1604 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-85]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1605)) (countLit q [-85]) (countLit q [-88]) (count1605 q) 1 (meaningNeg88 q) (meaning1605 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1605 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-85]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1605)) (countLit q [-85]) (countLit q [-88]) (count1605 q) 1 (meaningNeg85 q) (meaning1605 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1605 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-85]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1606)) (countLit q [-85]) (countLit q [-88]) (count1605 q) 1 1 (meaningNeg85 q) (meaningNeg88 q) (meaning1606 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 1606 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1607)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 1 (meaning1605 q) (meaning1607 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1607 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1608)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 2 (meaning1606 q) (meaning1608 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1608 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_left (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 1 (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1607 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1608)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 1 1 (meaning1603 q) (meaning1605 q) (meaning1608 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = false ∨ valuation q 1608 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1609 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1609)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 1 2 (meaning1603 q) (meaning1606 q) (meaning1609 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1606 = false ∨ valuation q 1609 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1608)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 2 (meaning1604 q) (meaning1608 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1608 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1609 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1609)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 2 1 (meaning1604 q) (meaning1605 q) (meaning1609 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1605 = false ∨ valuation q 1609 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E187.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112187
