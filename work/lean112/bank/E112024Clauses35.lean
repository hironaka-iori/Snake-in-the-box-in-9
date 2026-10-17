import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 6 (meaning1634 q) (meaning1642 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1638)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 1 (meaning1605 q) (meaning1629 q) (meaning1638 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1629 = false ∨ valuation q 1638 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1639)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 2 (meaning1605 q) (meaning1630 q) (meaning1639 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1630 = false ∨ valuation q 1639 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1640)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 3 (meaning1605 q) (meaning1631 q) (meaning1640 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1631 = false ∨ valuation q 1640 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1641)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 4 (meaning1605 q) (meaning1632 q) (meaning1641 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1632 = false ∨ valuation q 1641 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1642)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 5 (meaning1605 q) (meaning1633 q) (meaning1642 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1633 = false ∨ valuation q 1642 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 6 (meaning1605 q) (meaning1634 q) (meaning1643 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1634 = false ∨ valuation q 1643 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1639)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 1 (meaning1606 q) (meaning1629 q) (meaning1639 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1629 = false ∨ valuation q 1639 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1640)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 2 (meaning1606 q) (meaning1630 q) (meaning1640 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1630 = false ∨ valuation q 1640 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1641)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 3 (meaning1606 q) (meaning1631 q) (meaning1641 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1631 = false ∨ valuation q 1641 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1642)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 4 (meaning1606 q) (meaning1632 q) (meaning1642 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1632 = false ∨ valuation q 1642 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1643)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 5 (meaning1606 q) (meaning1633 q) (meaning1643 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1633 = false ∨ valuation q 1643 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1644 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 6 (meaning1606 q) (meaning1634 q) (meaning1644 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1634 = false ∨ valuation q 1644 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1640)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 1 (meaning1607 q) (meaning1629 q) (meaning1640 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1629 = false ∨ valuation q 1640 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1641)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 2 (meaning1607 q) (meaning1630 q) (meaning1641 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1630 = false ∨ valuation q 1641 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1642)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 3 (meaning1607 q) (meaning1631 q) (meaning1642 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1631 = false ∨ valuation q 1642 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1643)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 4 (meaning1607 q) (meaning1632 q) (meaning1643 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1632 = false ∨ valuation q 1643 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1644 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1644)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 5 (meaning1607 q) (meaning1633 q) (meaning1644 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1633 = false ∨ valuation q 1644 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1645 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 6 (meaning1607 q) (meaning1634 q) (meaning1645 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1634 = false ∨ valuation q 1645 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1642)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 2 (meaning1608 q) (meaning1630 q) (meaning1642 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1630 = false ∨ valuation q 1642 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1643)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 3 (meaning1608 q) (meaning1631 q) (meaning1643 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1631 = false ∨ valuation q 1643 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1644 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1644)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 4 (meaning1608 q) (meaning1632 q) (meaning1644 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1632 = false ∨ valuation q 1644 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1645 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1645)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 5 (meaning1608 q) (meaning1633 q) (meaning1645 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1633 = false ∨ valuation q 1645 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1653)) (countLit q [-91]) (countLit q [-93]) (count1653 q) 1 (meaningNeg93 q) (meaning1653 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1653 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1653)) (countLit q [-91]) (countLit q [-93]) (count1653 q) 1 (meaningNeg91 q) (meaning1653 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1653 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1654 = true := by
  have hs : count1653 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1654)) (countLit q [-91]) (countLit q [-93]) (count1653 q) 1 1 (meaningNeg91 q) (meaningNeg93 q) (meaning1654 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 1654 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1655)) (countLit q [-94]) (countLit q [-96]) (count1655 q) 1 (meaningNeg96 q) (meaning1655 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1655 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1655)) (countLit q [-94]) (countLit q [-96]) (count1655 q) 1 (meaningNeg94 q) (meaning1655 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1655 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1656)) (countLit q [-94]) (countLit q [-96]) (count1655 q) 1 1 (meaningNeg94 q) (meaningNeg96 q) (meaning1656 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 1656 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_right (literal (valuationOf q) (1655)) (literal (valuationOf q) (1657)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 1 (meaning1655 q) (meaning1657 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1657 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1658)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 2 (meaning1656 q) (meaning1658 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1658 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_left (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 1 (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E024.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112024
