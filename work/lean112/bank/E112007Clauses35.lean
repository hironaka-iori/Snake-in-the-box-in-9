import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1613)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 3 2 (meaning1584 q) (meaning1603 q) (meaning1613 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1603 = false ∨ valuation q 1613 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1614)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 3 3 (meaning1584 q) (meaning1604 q) (meaning1614 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1604 = false ∨ valuation q 1614 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1615)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 3 4 (meaning1584 q) (meaning1605 q) (meaning1615 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1605 = false ∨ valuation q 1615 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1616)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 3 5 (meaning1584 q) (meaning1606 q) (meaning1616 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1606 = false ∨ valuation q 1616 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1612)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 4 (meaning1585 q) (meaning1612 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1612 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1613)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 4 1 (meaning1585 q) (meaning1602 q) (meaning1613 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1602 = false ∨ valuation q 1613 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1614)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 4 2 (meaning1585 q) (meaning1603 q) (meaning1614 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1603 = false ∨ valuation q 1614 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1615)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 4 3 (meaning1585 q) (meaning1604 q) (meaning1615 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1604 = false ∨ valuation q 1615 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1616)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 4 4 (meaning1585 q) (meaning1605 q) (meaning1616 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1605 = false ∨ valuation q 1616 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1613)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 5 (meaning1586 q) (meaning1613 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1613 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1614 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1614)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 5 1 (meaning1586 q) (meaning1602 q) (meaning1614 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1602 = false ∨ valuation q 1614 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1615 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1615)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 5 2 (meaning1586 q) (meaning1603 q) (meaning1615 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1603 = false ∨ valuation q 1615 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 5 3 (meaning1586 q) (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true := by
  have hs : count1609 q = (countLit q [-61, -64, -65, -67, -68, -72, -74]) + (countLit q [-76, -77, -81, -83, -85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74]) (l₂ := [-76, -77, -81, -83, -85, -86, -90])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1617)) (countLit q [-61, -64, -65, -67, -68, -72, -74]) (countLit q [-76, -77, -81, -83, -85, -86, -90]) (count1609 q) 5 4 (meaning1586 q) (meaning1605 q) (meaning1617 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1605 = false ∨ valuation q 1617 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1623)) (countLit q [-93]) (countLit q [-94]) (count1623 q) 1 (meaningNeg94 q) (meaning1623 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1623 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1623)) (countLit q [-93]) (countLit q [-94]) (count1623 q) 1 (meaningNeg93 q) (meaning1623 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1623 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1624)) (countLit q [-93]) (countLit q [-94]) (count1623 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1624 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1624 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1623)) (literal (valuationOf q) (1625)) (countLit q [-92]) (countLit q [-93, -94]) (count1625 q) 1 (meaning1623 q) (meaning1625 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1625 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1624)) (literal (valuationOf q) (1626)) (countLit q [-92]) (countLit q [-93, -94]) (count1625 q) 2 (meaning1624 q) (meaning1626 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1626 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1625)) (countLit q [-92]) (countLit q [-93, -94]) (count1625 q) 1 (meaningNeg92 q) (meaning1625 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1625 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1626)) (countLit q [-92]) (countLit q [-93, -94]) (count1625 q) 1 1 (meaningNeg92 q) (meaning1623 q) (meaning1626 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1623 = false ∨ valuation q 1626 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1627)) (countLit q [-92]) (countLit q [-93, -94]) (count1625 q) 1 2 (meaningNeg92 q) (meaning1624 q) (meaning1627 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1624 = false ∨ valuation q 1627 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1628)) (countLit q [-97]) (countLit q [-98]) (count1628 q) 1 (meaningNeg98 q) (meaning1628 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1628 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1628)) (countLit q [-97]) (countLit q [-98]) (count1628 q) 1 (meaningNeg97 q) (meaning1628 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1628 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1629 = true := by
  have hs : count1628 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1629)) (countLit q [-97]) (countLit q [-98]) (count1628 q) 1 1 (meaningNeg97 q) (meaningNeg98 q) (meaning1629 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 1629 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1630)) (countLit q [-102]) (countLit q [-104]) (count1630 q) 1 (meaningNeg104 q) (meaning1630 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1630 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1630)) (countLit q [-102]) (countLit q [-104]) (count1630 q) 1 (meaningNeg102 q) (meaning1630 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1630 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1631)) (countLit q [-102]) (countLit q [-104]) (count1630 q) 1 1 (meaningNeg102 q) (meaningNeg104 q) (meaning1631 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 1631 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1632)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 1 (meaning1630 q) (meaning1632 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1632 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (1631)) (literal (valuationOf q) (1633)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 2 (meaning1631 q) (meaning1633 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_left (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 1 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 1 1 (meaning1628 q) (meaning1630 q) (meaning1633 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1630 = false ∨ valuation q 1633 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E007.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112007
