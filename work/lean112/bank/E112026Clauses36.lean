import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1640)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 (meaning1632 q) (meaning1640 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1640 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1641)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 5 (meaning1633 q) (meaning1641 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1641 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 6 (meaning1634 q) (meaning1642 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 7 (meaning1635 q) (meaning1643 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1638)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 1 (meaning1605 q) (meaning1629 q) (meaning1638 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1629 = false ∨ valuation q 1638 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1639)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 2 (meaning1605 q) (meaning1630 q) (meaning1639 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1630 = false ∨ valuation q 1639 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1640)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 3 (meaning1605 q) (meaning1631 q) (meaning1640 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1631 = false ∨ valuation q 1640 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1641)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 4 (meaning1605 q) (meaning1632 q) (meaning1641 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1632 = false ∨ valuation q 1641 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1642)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 5 (meaning1605 q) (meaning1633 q) (meaning1642 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1633 = false ∨ valuation q 1642 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 6 (meaning1605 q) (meaning1634 q) (meaning1643 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1634 = false ∨ valuation q 1643 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1639)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 1 (meaning1606 q) (meaning1629 q) (meaning1639 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1629 = false ∨ valuation q 1639 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1640)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 2 (meaning1606 q) (meaning1630 q) (meaning1640 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1630 = false ∨ valuation q 1640 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1641)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 3 (meaning1606 q) (meaning1631 q) (meaning1641 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1631 = false ∨ valuation q 1641 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1642)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 4 (meaning1606 q) (meaning1632 q) (meaning1642 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1632 = false ∨ valuation q 1642 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1643)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 5 (meaning1606 q) (meaning1633 q) (meaning1643 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1633 = false ∨ valuation q 1643 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1644 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 6 (meaning1606 q) (meaning1634 q) (meaning1644 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1634 = false ∨ valuation q 1644 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1645 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1635)) (literal (valuationOf q) (1645)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 7 (meaning1606 q) (meaning1635 q) (meaning1645 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1635 = false ∨ valuation q 1645 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1640)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 1 (meaning1607 q) (meaning1629 q) (meaning1640 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1629 = false ∨ valuation q 1640 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1641)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 2 (meaning1607 q) (meaning1630 q) (meaning1641 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1630 = false ∨ valuation q 1641 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1642)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 3 (meaning1607 q) (meaning1631 q) (meaning1642 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1631 = false ∨ valuation q 1642 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1643)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 4 (meaning1607 q) (meaning1632 q) (meaning1643 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1632 = false ∨ valuation q 1643 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1644 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1644)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 5 (meaning1607 q) (meaning1633 q) (meaning1644 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1633 = false ∨ valuation q 1644 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1645 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 6 (meaning1607 q) (meaning1634 q) (meaning1645 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1634 = false ∨ valuation q 1645 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1642 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1642)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 2 (meaning1608 q) (meaning1630 q) (meaning1642 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1630 = false ∨ valuation q 1642 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1643 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1643)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 3 (meaning1608 q) (meaning1631 q) (meaning1643 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1631 = false ∨ valuation q 1643 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1644 = true := by
  have hs : count1637 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1644)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 4 (meaning1608 q) (meaning1632 q) (meaning1644 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1632 = false ∨ valuation q 1644 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1653)) (countLit q [-91]) (countLit q [-93]) (count1653 q) 1 (meaningNeg93 q) (meaning1653 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1653 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1653)) (countLit q [-91]) (countLit q [-93]) (count1653 q) 1 (meaningNeg91 q) (meaning1653 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1653 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1654 = true := by
  have hs : count1653 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1654)) (countLit q [-91]) (countLit q [-93]) (count1653 q) 1 1 (meaningNeg91 q) (meaningNeg93 q) (meaning1654 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 1654 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1655)) (countLit q [-94]) (countLit q [-96]) (count1655 q) 1 (meaningNeg96 q) (meaning1655 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1655 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1655)) (countLit q [-94]) (countLit q [-96]) (count1655 q) 1 (meaningNeg94 q) (meaning1655 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1655 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1656)) (countLit q [-94]) (countLit q [-96]) (count1655 q) 1 1 (meaningNeg94 q) (meaningNeg96 q) (meaning1656 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 1656 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E026.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112026
