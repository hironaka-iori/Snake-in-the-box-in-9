import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1580)) (countLit q [-42]) (countLit q [-45]) (count1580 q) 1 (meaningNeg42 q) (meaning1580 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1580 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1581)) (countLit q [-42]) (countLit q [-45]) (count1580 q) 1 1 (meaningNeg42 q) (meaningNeg45 q) (meaning1581 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 1581 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1582)) (countLit q [-47]) (countLit q [-48]) (count1582 q) 1 (meaningNeg48 q) (meaning1582 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1582 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1582)) (countLit q [-47]) (countLit q [-48]) (count1582 q) 1 (meaningNeg47 q) (meaning1582 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1582 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1583)) (countLit q [-47]) (countLit q [-48]) (count1582 q) 1 1 (meaningNeg47 q) (meaningNeg48 q) (meaning1583 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 1583 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1584)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 1 (meaning1582 q) (meaning1584 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1584 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 2 (meaning1583 q) (meaning1585 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 1 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1585)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 1 1 (meaning1580 q) (meaning1582 q) (meaning1585 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = false ∨ valuation q 1585 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 1 2 (meaning1580 q) (meaning1583 q) (meaning1586 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1583 = false ∨ valuation q 1586 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 2 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 2 1 (meaning1581 q) (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1582 = false ∨ valuation q 1586 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1584 q) 2 2 (meaning1581 q) (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-49]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1588)) (countLit q [-49]) (countLit q [-53]) (count1588 q) 1 (meaningNeg53 q) (meaning1588 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1588 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-49]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1588)) (countLit q [-49]) (countLit q [-53]) (count1588 q) 1 (meaningNeg49 q) (meaning1588 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1588 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1589 = true := by
  have hs : count1588 q = (countLit q [-49]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1589)) (countLit q [-49]) (countLit q [-53]) (count1588 q) 1 1 (meaningNeg49 q) (meaningNeg53 q) (meaning1589 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 53 = true ∨ valuation q 1589 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1590)) (countLit q [-54]) (countLit q [-56]) (count1590 q) 1 (meaningNeg56 q) (meaning1590 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1590 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1590)) (countLit q [-54]) (countLit q [-56]) (count1590 q) 1 (meaningNeg54 q) (meaning1590 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1590 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1591 = true := by
  have hs : count1590 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1591)) (countLit q [-54]) (countLit q [-56]) (count1590 q) 1 1 (meaningNeg54 q) (meaningNeg56 q) (meaning1591 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 1591 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1592)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 1 (meaning1590 q) (meaning1592 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1592 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1593)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 2 (meaning1591 q) (meaning1593 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1593 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_left (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 1 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1593)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 1 1 (meaning1588 q) (meaning1590 q) (meaning1593 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = false ∨ valuation q 1593 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1594)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 1 2 (meaning1588 q) (meaning1591 q) (meaning1594 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1591 = false ∨ valuation q 1594 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_left (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 2 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 2 1 (meaning1589 q) (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1590 = false ∨ valuation q 1594 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1595 = true := by
  have hs : count1592 q = (countLit q [-49, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-49, -53]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1595)) (countLit q [-49, -53]) (countLit q [-54, -56]) (count1592 q) 2 2 (meaning1589 q) (meaning1591 q) (meaning1595 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = false ∨ valuation q 1595 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-42, -45, -47, -48]) + (countLit q [-49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -47, -48]) (l₂ := [-49, -53, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1592)) (literal (valuationOf q) (1596)) (countLit q [-42, -45, -47, -48]) (countLit q [-49, -53, -54, -56]) (count1596 q) 1 (meaning1592 q) (meaning1596 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1596 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-42, -45, -47, -48]) + (countLit q [-49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -47, -48]) (l₂ := [-49, -53, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1593)) (literal (valuationOf q) (1597)) (countLit q [-42, -45, -47, -48]) (countLit q [-49, -53, -54, -56]) (count1596 q) 2 (meaning1593 q) (meaning1597 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1597 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1598 = true := by
  have hs : count1596 q = (countLit q [-42, -45, -47, -48]) + (countLit q [-49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -47, -48]) (l₂ := [-49, -53, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1594)) (literal (valuationOf q) (1598)) (countLit q [-42, -45, -47, -48]) (countLit q [-49, -53, -54, -56]) (count1596 q) 3 (meaning1594 q) (meaning1598 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1598 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1599 = true := by
  have hs : count1596 q = (countLit q [-42, -45, -47, -48]) + (countLit q [-49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -47, -48]) (l₂ := [-49, -53, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1595)) (literal (valuationOf q) (1599)) (countLit q [-42, -45, -47, -48]) (countLit q [-49, -53, -54, -56]) (count1596 q) 4 (meaning1595 q) (meaning1599 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1599 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-42, -45, -47, -48]) + (countLit q [-49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -47, -48]) (l₂ := [-49, -53, -54, -56])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1596)) (countLit q [-42, -45, -47, -48]) (countLit q [-49, -53, -54, -56]) (count1596 q) 1 (meaning1584 q) (meaning1596 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1596 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E020.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112020
