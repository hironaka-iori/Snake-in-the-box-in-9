import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1625)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 1 2 (meaning1612 q) (meaning1620 q) (meaning1625 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1620 = false ∨ valuation q 1625 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1626)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 1 3 (meaning1612 q) (meaning1621 q) (meaning1626 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1627)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 1 4 (meaning1612 q) (meaning1622 q) (meaning1627 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_left (literal (valuationOf q) (1613)) (literal (valuationOf q) (1624)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 2 (meaning1613 q) (meaning1624 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1624 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 2 1 (meaning1613 q) (meaning1619 q) (meaning1625 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1626)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 2 2 (meaning1613 q) (meaning1620 q) (meaning1626 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1620 = false ∨ valuation q 1626 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1627)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 2 3 (meaning1613 q) (meaning1621 q) (meaning1627 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1628 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1628)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 2 4 (meaning1613 q) (meaning1622 q) (meaning1628 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1622 = false ∨ valuation q 1628 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_left (literal (valuationOf q) (1614)) (literal (valuationOf q) (1625)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 3 (meaning1614 q) (meaning1625 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1625 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1626)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 3 1 (meaning1614 q) (meaning1619 q) (meaning1626 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1619 = false ∨ valuation q 1626 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1627)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 3 2 (meaning1614 q) (meaning1620 q) (meaning1627 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1620 = false ∨ valuation q 1627 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1630)) (countLit q [-104]) (countLit q [-107]) (count1630 q) 1 (meaningNeg107 q) (meaning1630 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1630 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1630)) (countLit q [-104]) (countLit q [-107]) (count1630 q) 1 (meaningNeg104 q) (meaning1630 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1630 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1631)) (countLit q [-104]) (countLit q [-107]) (count1630 q) 1 1 (meaningNeg104 q) (meaningNeg107 q) (meaning1631 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 1631 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1632)) (countLit q [-109]) (countLit q [-110]) (count1632 q) 1 (meaningNeg110 q) (meaning1632 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1632 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1632)) (countLit q [-109]) (countLit q [-110]) (count1632 q) 1 (meaningNeg109 q) (meaning1632 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1632 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1633)) (countLit q [-109]) (countLit q [-110]) (count1632 q) 1 1 (meaningNeg109 q) (meaningNeg110 q) (meaning1633 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 1633 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 2 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_left (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 1 (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 1 1 (meaning1630 q) (meaning1632 q) (meaning1635 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1632 = false ∨ valuation q 1635 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 1 2 (meaning1630 q) (meaning1633 q) (meaning1636 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_left (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 2 (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1635 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 2 1 (meaning1631 q) (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1632 = false ∨ valuation q 1636 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1634 q) 2 2 (meaning1631 q) (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = false ∨ valuation q 1637 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1638)) (countLit q [-112]) (countLit q [-113]) (count1638 q) 1 (meaningNeg113 q) (meaning1638 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1638 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1638)) (countLit q [-112]) (countLit q [-113]) (count1638 q) 1 (meaningNeg112 q) (meaning1638 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1638 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1639)) (countLit q [-112]) (countLit q [-113]) (count1638 q) 1 1 (meaningNeg112 q) (meaningNeg113 q) (meaning1639 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 1639 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1640)) (countLit q [-115]) (countLit q [-117]) (count1640 q) 1 (meaningNeg117 q) (meaning1640 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1640 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1640)) (countLit q [-115]) (countLit q [-117]) (count1640 q) 1 (meaningNeg115 q) (meaning1640 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1640 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1641)) (countLit q [-115]) (countLit q [-117]) (count1640 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1641 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1641 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 1 (meaning1640 q) (meaning1642 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E110.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112110
