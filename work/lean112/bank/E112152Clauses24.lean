import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1638 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1638)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 2 4 (meaning1603 q) (meaning1628 q) (meaning1638 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1628 = false ∨ valuation q 1638 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1635 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1635)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 3 (meaning1604 q) (meaning1635 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1635 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1636 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1636)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 3 1 (meaning1604 q) (meaning1625 q) (meaning1636 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1625 = false ∨ valuation q 1636 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1637 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1637)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 3 2 (meaning1604 q) (meaning1626 q) (meaning1637 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1626 = false ∨ valuation q 1637 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1638 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1638)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 3 3 (meaning1604 q) (meaning1627 q) (meaning1638 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1627 = false ∨ valuation q 1638 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1639 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1639)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 3 4 (meaning1604 q) (meaning1628 q) (meaning1639 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1628 = false ∨ valuation q 1639 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1637 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1637)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 4 1 (meaning1605 q) (meaning1625 q) (meaning1637 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1625 = false ∨ valuation q 1637 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1638 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1638)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 4 2 (meaning1605 q) (meaning1626 q) (meaning1638 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1626 = false ∨ valuation q 1638 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1639 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1639)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 4 3 (meaning1605 q) (meaning1627 q) (meaning1639 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1627 = false ∨ valuation q 1639 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1640 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1640)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 4 4 (meaning1605 q) (meaning1628 q) (meaning1640 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1628 = false ∨ valuation q 1640 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1639 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1639)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 5 2 (meaning1606 q) (meaning1626 q) (meaning1639 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1626 = false ∨ valuation q 1639 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1640 = true := by
  have hs : count1633 q = (countLit q [-62, -63, -64, -65, -67, -70, -73]) + (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73]) (l₂ := [-74, -76, -79, -80, -81, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1640)) (countLit q [-62, -63, -64, -65, -67, -70, -73]) (countLit q [-74, -76, -79, -80, -81, -84, -86, -88]) (count1633 q) 5 3 (meaning1606 q) (meaning1627 q) (meaning1640 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1627 = false ∨ valuation q 1640 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1648)) (countLit q [-91]) (countLit q [-94]) (count1648 q) 1 (meaningNeg94 q) (meaning1648 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1648 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1648)) (countLit q [-91]) (countLit q [-94]) (count1648 q) 1 (meaningNeg91 q) (meaning1648 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1648 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1649)) (countLit q [-91]) (countLit q [-94]) (count1648 q) 1 1 (meaningNeg91 q) (meaningNeg94 q) (meaning1649 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 1649 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -94])
  have hm := merge_right (literal (valuationOf q) (1648)) (literal (valuationOf q) (1650)) (countLit q [-90]) (countLit q [-91, -94]) (count1650 q) 1 (meaning1648 q) (meaning1650 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1650 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -94])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1651)) (countLit q [-90]) (countLit q [-91, -94]) (count1650 q) 2 (meaning1649 q) (meaning1651 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1651 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -94])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1650)) (countLit q [-90]) (countLit q [-91, -94]) (count1650 q) 1 (meaningNeg90 q) (meaning1650 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1650 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1648 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1651)) (countLit q [-90]) (countLit q [-91, -94]) (count1650 q) 1 1 (meaningNeg90 q) (meaning1648 q) (meaning1651 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1648 = false ∨ valuation q 1651 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1649 = false ∨ valuationOf q 1652 = true := by
  have hs : count1650 q = (countLit q [-90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1652)) (countLit q [-90]) (countLit q [-91, -94]) (count1650 q) 1 2 (meaningNeg90 q) (meaning1649 q) (meaning1652 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1649 = false ∨ valuation q 1652 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1653)) (countLit q [-96]) (countLit q [-99]) (count1653 q) 1 (meaningNeg99 q) (meaning1653 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1653 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1653)) (countLit q [-96]) (countLit q [-99]) (count1653 q) 1 (meaningNeg96 q) (meaning1653 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1653 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1654 = true := by
  have hs : count1653 q = (countLit q [-96]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1654)) (countLit q [-96]) (countLit q [-99]) (count1653 q) 1 1 (meaningNeg96 q) (meaningNeg99 q) (meaning1654 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 1654 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-100]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1655)) (countLit q [-100]) (countLit q [-104]) (count1655 q) 1 (meaningNeg104 q) (meaning1655 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1655 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-100]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1655)) (countLit q [-100]) (countLit q [-104]) (count1655 q) 1 (meaningNeg100 q) (meaning1655 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1655 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-100]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1656)) (countLit q [-100]) (countLit q [-104]) (count1655 q) 1 1 (meaningNeg100 q) (meaningNeg104 q) (meaning1656 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 104 = true ∨ valuation q 1656 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_right (literal (valuationOf q) (1655)) (literal (valuationOf q) (1657)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 1 (meaning1655 q) (meaning1657 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1657 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1658)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 2 (meaning1656 q) (meaning1658 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1658 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_left (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 1 (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1657 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1658)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 1 1 (meaning1653 q) (meaning1655 q) (meaning1658 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = false ∨ valuation q 1658 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1659 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1659)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 1 2 (meaning1653 q) (meaning1656 q) (meaning1659 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1656 = false ∨ valuation q 1659 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_left (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 2 (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1658 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E152.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112152
