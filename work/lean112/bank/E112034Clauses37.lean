import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1598)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 5 6 (meaning1560 q) (meaning1585 q) (meaning1598 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1585 = false ∨ valuation q 1598 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1600 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1600)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 5 8 (meaning1560 q) (meaning1587 q) (meaning1600 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1587 = false ∨ valuation q 1600 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1595)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 6 2 (meaning1561 q) (meaning1581 q) (meaning1595 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1581 = false ∨ valuation q 1595 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1596)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 6 3 (meaning1561 q) (meaning1582 q) (meaning1596 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1582 = false ∨ valuation q 1596 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1598)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 6 5 (meaning1561 q) (meaning1584 q) (meaning1598 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1584 = false ∨ valuation q 1598 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1596)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 7 2 (meaning1562 q) (meaning1581 q) (meaning1596 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1581 = false ∨ valuation q 1596 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1604)) (countLit q [-28]) (countLit q [-29]) (count1604 q) 1 (meaningNeg29 q) (meaning1604 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1604 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1604)) (countLit q [-28]) (countLit q [-29]) (count1604 q) 1 (meaningNeg28 q) (meaning1604 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1604 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1605)) (countLit q [-28]) (countLit q [-29]) (count1604 q) 1 1 (meaningNeg28 q) (meaningNeg29 q) (meaning1605 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 29 = true ∨ valuation q 1605 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1606 = true := by
  have hs : count1606 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1606)) (countLit q [-33]) (countLit q [-35]) (count1606 q) 1 (meaningNeg35 q) (meaning1606 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1606 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1606 = true := by
  have hs : count1606 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1606)) (countLit q [-33]) (countLit q [-35]) (count1606 q) 1 (meaningNeg33 q) (meaning1606 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1606 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1607 = true := by
  have hs : count1606 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1607)) (countLit q [-33]) (countLit q [-35]) (count1606 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning1607 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 1607 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1608)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 1 (meaning1606 q) (meaning1608 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1608 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1609)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 2 (meaning1607 q) (meaning1609 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1609 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1608)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 1 (meaning1604 q) (meaning1608 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1608 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1609)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 1 1 (meaning1604 q) (meaning1606 q) (meaning1609 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1606 = false ∨ valuation q 1609 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1610 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1610)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 1 2 (meaning1604 q) (meaning1607 q) (meaning1610 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1607 = false ∨ valuation q 1610 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (1605)) (literal (valuationOf q) (1609)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 2 (meaning1605 q) (meaning1609 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1609 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1610 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1610)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 2 1 (meaning1605 q) (meaning1606 q) (meaning1610 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1606 = false ∨ valuation q 1610 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1608 q = (countLit q [-28, -29]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-28, -29]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-28, -29]) (countLit q [-33, -35]) (count1608 q) 2 2 (meaning1605 q) (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1607 = false ∨ valuation q 1611 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1612)) (countLit q [-36]) (countLit q [-37]) (count1612 q) 1 (meaningNeg37 q) (meaning1612 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1612 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1612)) (countLit q [-36]) (countLit q [-37]) (count1612 q) 1 (meaningNeg36 q) (meaning1612 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1612 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1613)) (countLit q [-36]) (countLit q [-37]) (count1612 q) 1 1 (meaningNeg36 q) (meaningNeg37 q) (meaning1613 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 1613 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1614)) (countLit q [-40]) (countLit q [-42]) (count1614 q) 1 (meaningNeg42 q) (meaning1614 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1614 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1614)) (countLit q [-40]) (countLit q [-42]) (count1614 q) 1 (meaningNeg40 q) (meaning1614 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1614 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1615)) (countLit q [-40]) (countLit q [-42]) (count1614 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1615 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1615 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1614)) (literal (valuationOf q) (1616)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 1 (meaning1614 q) (meaning1616 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1616 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 2 (meaning1615 q) (meaning1617 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1612)) (literal (valuationOf q) (1616)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 1 (meaning1612 q) (meaning1616 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1616 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1617)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 1 1 (meaning1612 q) (meaning1614 q) (meaning1617 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1614 = false ∨ valuation q 1617 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 1 2 (meaning1612 q) (meaning1615 q) (meaning1618 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1615 = false ∨ valuation q 1618 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1613)) (literal (valuationOf q) (1617)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1616 q) 2 (meaning1613 q) (meaning1617 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1617 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E034.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112034
