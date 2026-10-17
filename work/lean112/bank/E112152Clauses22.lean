import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-65, -67]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -73])
  have hm := merge_right (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (countLit q [-65, -67]) (countLit q [-70, -73]) (count1598 q) 1 (meaning1596 q) (meaning1598 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-65, -67]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -73])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1598)) (countLit q [-65, -67]) (countLit q [-70, -73]) (count1598 q) 1 (meaning1594 q) (meaning1598 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1598 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-65, -67]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -73])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1599)) (countLit q [-65, -67]) (countLit q [-70, -73]) (count1598 q) 1 1 (meaning1594 q) (meaning1596 q) (meaning1599 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1596 = false ∨ valuation q 1599 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-65, -67]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -73])
  have hm := merge_left (literal (valuationOf q) (1595)) (literal (valuationOf q) (1599)) (countLit q [-65, -67]) (countLit q [-70, -73]) (count1598 q) 2 (meaning1595 q) (meaning1599 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1599 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1600 = true := by
  have hs : count1598 q = (countLit q [-65, -67]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-70, -73])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1600)) (countLit q [-65, -67]) (countLit q [-70, -73]) (count1598 q) 2 1 (meaning1595 q) (meaning1596 q) (meaning1600 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1596 = false ∨ valuation q 1600 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 1 (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1602 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1603)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 2 (meaning1599 q) (meaning1603 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1603 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 3 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_left (literal (valuationOf q) (1591)) (literal (valuationOf q) (1602)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 1 (meaning1591 q) (meaning1602 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1602 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1603)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 1 1 (meaning1591 q) (meaning1598 q) (meaning1603 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1598 = false ∨ valuation q 1603 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1604)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 1 2 (meaning1591 q) (meaning1599 q) (meaning1604 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1599 = false ∨ valuation q 1604 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1605)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 1 3 (meaning1591 q) (meaning1600 q) (meaning1605 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1600 = false ∨ valuation q 1605 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_left (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 2 (meaning1592 q) (meaning1603 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1603 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1604)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 2 1 (meaning1592 q) (meaning1598 q) (meaning1604 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1598 = false ∨ valuation q 1604 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1605)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 2 2 (meaning1592 q) (meaning1599 q) (meaning1605 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1599 = false ∨ valuation q 1605 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1606)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 2 3 (meaning1592 q) (meaning1600 q) (meaning1606 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1600 = false ∨ valuation q 1606 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1604)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 3 (meaning1593 q) (meaning1604 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1604 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1605)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 3 1 (meaning1593 q) (meaning1598 q) (meaning1605 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1598 = false ∨ valuation q 1605 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-62, -63, -64]) + (countLit q [-65, -67, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64]) (l₂ := [-65, -67, -70, -73])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1606)) (countLit q [-62, -63, -64]) (countLit q [-65, -67, -70, -73]) (count1602 q) 3 2 (meaning1593 q) (meaning1599 q) (meaning1606 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1599 = false ∨ valuation q 1606 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1609)) (countLit q [-74]) (countLit q [-76]) (count1609 q) 1 (meaningNeg76 q) (meaning1609 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1609 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1609)) (countLit q [-74]) (countLit q [-76]) (count1609 q) 1 (meaningNeg74 q) (meaning1609 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1609 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1610)) (countLit q [-74]) (countLit q [-76]) (count1609 q) 1 1 (meaningNeg74 q) (meaningNeg76 q) (meaning1610 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 1610 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1611)) (countLit q [-79]) (countLit q [-80]) (count1611 q) 1 (meaningNeg80 q) (meaning1611 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1611 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1611)) (countLit q [-79]) (countLit q [-80]) (count1611 q) 1 (meaningNeg79 q) (meaning1611 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1611 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1612)) (countLit q [-79]) (countLit q [-80]) (count1611 q) 1 1 (meaningNeg79 q) (meaningNeg80 q) (meaning1612 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 80 = true ∨ valuation q 1612 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-74, -76]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-74, -76]) (countLit q [-79, -80]) (count1613 q) 1 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1614 = true := by
  have hs : count1613 q = (countLit q [-74, -76]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1614)) (countLit q [-74, -76]) (countLit q [-79, -80]) (count1613 q) 2 (meaning1612 q) (meaning1614 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1614 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-74, -76]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -80])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-74, -76]) (countLit q [-79, -80]) (count1613 q) 1 (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1613 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true := by
  have hs : count1613 q = (countLit q [-74, -76]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1614)) (countLit q [-74, -76]) (countLit q [-79, -80]) (count1613 q) 1 1 (meaning1609 q) (meaning1611 q) (meaning1614 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1611 = false ∨ valuation q 1614 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1615 = true := by
  have hs : count1613 q = (countLit q [-74, -76]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1615)) (countLit q [-74, -76]) (countLit q [-79, -80]) (count1613 q) 1 2 (meaning1609 q) (meaning1612 q) (meaning1615 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1612 = false ∨ valuation q 1615 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1615 = true := by
  have hs : count1613 q = (countLit q [-74, -76]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1615)) (countLit q [-74, -76]) (countLit q [-79, -80]) (count1613 q) 2 1 (meaning1610 q) (meaning1611 q) (meaning1615 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1611 = false ∨ valuation q 1615 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-81]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1617)) (countLit q [-81]) (countLit q [-84]) (count1617 q) 1 (meaningNeg84 q) (meaning1617 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1617 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E152.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112152
