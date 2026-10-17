import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-110]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-110)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1609)) (countLit q [-110]) (countLit q [-112]) (count1608 q) 1 1 (meaningNeg110 q) (meaningNeg112 q) (meaning1609 q) hs
  change (! (valuationOf q 110)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 1609 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1610)) (countLit q [-113]) (countLit q [-114]) (count1610 q) 1 (meaningNeg114 q) (meaning1610 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1610 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1610)) (countLit q [-113]) (countLit q [-114]) (count1610 q) 1 (meaningNeg113 q) (meaning1610 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1610 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1611)) (countLit q [-113]) (countLit q [-114]) (count1610 q) 1 1 (meaningNeg113 q) (meaningNeg114 q) (meaning1611 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 1611 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-110, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-110, -112]) (countLit q [-113, -114]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-110, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-110, -112]) (countLit q [-113, -114]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-110, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-110, -112]) (countLit q [-113, -114]) (count1612 q) 1 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-110, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-110, -112]) (countLit q [-113, -114]) (count1612 q) 1 1 (meaning1608 q) (meaning1610 q) (meaning1613 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-110, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-110, -112]) (countLit q [-113, -114]) (count1612 q) 2 (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1613 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 1 (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1617)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 1 1 (meaning1604 q) (meaning1612 q) (meaning1617 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1612 = false ∨ valuation q 1617 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1618)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 1 2 (meaning1604 q) (meaning1613 q) (meaning1618 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1613 = false ∨ valuation q 1618 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (1605)) (literal (valuationOf q) (1617)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 2 (meaning1605 q) (meaning1617 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1617 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1618)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 2 1 (meaning1605 q) (meaning1612 q) (meaning1618 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1612 = false ∨ valuation q 1618 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 2 2 (meaning1605 q) (meaning1613 q) (meaning1619 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1613 = false ∨ valuation q 1619 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (1606)) (literal (valuationOf q) (1618)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 3 (meaning1606 q) (meaning1618 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1618 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -105, -106]) + (countLit q [-110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -105, -106]) (l₂ := [-110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (countLit q [-102, -103, -105, -106]) (countLit q [-110, -112, -113, -114]) (count1616 q) 3 1 (meaning1606 q) (meaning1612 q) (meaning1619 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1612 = false ∨ valuation q 1619 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1624 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (1616)) (literal (valuationOf q) (1624)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 1 (meaning1616 q) (meaning1624 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1624 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1625 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1625)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 2 (meaning1617 q) (meaning1625 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1625 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (1618)) (literal (valuationOf q) (1626)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 3 (meaning1618 q) (meaning1626 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1626 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1627)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 4 (meaning1619 q) (meaning1627 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1627 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1626)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 1 2 (meaning1593 q) (meaning1617 q) (meaning1626 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1617 = false ∨ valuation q 1626 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1627)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 1 3 (meaning1593 q) (meaning1618 q) (meaning1627 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1618 = false ∨ valuation q 1627 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1628)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 1 4 (meaning1593 q) (meaning1619 q) (meaning1628 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1619 = false ∨ valuation q 1628 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1626)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 2 1 (meaning1594 q) (meaning1616 q) (meaning1626 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1616 = false ∨ valuation q 1626 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1627)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 2 2 (meaning1594 q) (meaning1617 q) (meaning1627 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1617 = false ∨ valuation q 1627 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 2 3 (meaning1594 q) (meaning1618 q) (meaning1628 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1618 = false ∨ valuation q 1628 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_left (literal (valuationOf q) (1595)) (literal (valuationOf q) (1626)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 3 (meaning1595 q) (meaning1626 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1626 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1627)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 3 1 (meaning1595 q) (meaning1616 q) (meaning1627 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1616 = false ∨ valuation q 1627 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1628)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 3 2 (meaning1595 q) (meaning1617 q) (meaning1628 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1617 = false ∨ valuation q 1628 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1629)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 3 3 (meaning1595 q) (meaning1618 q) (meaning1629 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1618 = false ∨ valuation q 1629 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1628)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 4 1 (meaning1596 q) (meaning1616 q) (meaning1628 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1616 = false ∨ valuation q 1628 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E169.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112169
