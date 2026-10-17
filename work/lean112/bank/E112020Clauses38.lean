import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) + (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34, -35, -37, -38, -40]) (l₂ := [-42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1609)) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) (count1604 q) 5 1 (meaning1576 q) (meaning1596 q) (meaning1609 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1596 = false ∨ valuation q 1609 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) + (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34, -35, -37, -38, -40]) (l₂ := [-42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1610)) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) (count1604 q) 5 2 (meaning1576 q) (meaning1597 q) (meaning1610 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1597 = false ∨ valuation q 1610 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1611 = true := by
  have hs : count1604 q = (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) + (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34, -35, -37, -38, -40]) (l₂ := [-42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1611)) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) (count1604 q) 5 3 (meaning1576 q) (meaning1598 q) (meaning1611 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1598 = false ∨ valuation q 1611 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1612 = true := by
  have hs : count1604 q = (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) + (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34, -35, -37, -38, -40]) (l₂ := [-42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1612)) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) (count1604 q) 5 4 (meaning1576 q) (meaning1599 q) (meaning1612 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1599 = false ∨ valuation q 1612 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1613 = true := by
  have hs : count1604 q = (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) + (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34, -35, -37, -38, -40]) (l₂ := [-42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1613)) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) (count1604 q) 5 5 (meaning1576 q) (meaning1600 q) (meaning1613 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1600 = false ∨ valuation q 1613 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1614 = true := by
  have hs : count1604 q = (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) + (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34, -35, -37, -38, -40]) (l₂ := [-42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1614)) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) (count1604 q) 5 6 (meaning1576 q) (meaning1601 q) (meaning1614 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1601 = false ∨ valuation q 1614 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1612 = true := by
  have hs : count1604 q = (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) + (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34, -35, -37, -38, -40]) (l₂ := [-42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1612)) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40]) (countLit q [-42, -45, -47, -48, -49, -53, -54, -56]) (count1604 q) 6 3 (meaning1577 q) (meaning1598 q) (meaning1612 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1598 = false ∨ valuation q 1612 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1629)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 5 5 (meaning1545 q) (meaning1608 q) (meaning1629 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1608 = false ∨ valuation q 1629 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1630)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 5 6 (meaning1545 q) (meaning1609 q) (meaning1630 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1609 = false ∨ valuation q 1630 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1631)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 5 7 (meaning1545 q) (meaning1610 q) (meaning1631 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1610 = false ∨ valuation q 1631 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1632)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 5 8 (meaning1545 q) (meaning1611 q) (meaning1632 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1611 = false ∨ valuation q 1632 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1633)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 5 9 (meaning1545 q) (meaning1612 q) (meaning1633 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1612 = false ∨ valuation q 1633 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1634)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 5 10 (meaning1545 q) (meaning1613 q) (meaning1634 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1613 = false ∨ valuation q 1634 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1635 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1635)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 5 11 (meaning1545 q) (meaning1614 q) (meaning1635 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1614 = false ∨ valuation q 1635 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1629)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 6 4 (meaning1546 q) (meaning1607 q) (meaning1629 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1607 = false ∨ valuation q 1629 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1630)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 6 5 (meaning1546 q) (meaning1608 q) (meaning1630 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1608 = false ∨ valuation q 1630 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1631)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 6 6 (meaning1546 q) (meaning1609 q) (meaning1631 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1609 = false ∨ valuation q 1631 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1632)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 6 7 (meaning1546 q) (meaning1610 q) (meaning1632 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1610 = false ∨ valuation q 1632 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1633)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 6 8 (meaning1546 q) (meaning1611 q) (meaning1633 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1611 = false ∨ valuation q 1633 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1634)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 6 9 (meaning1546 q) (meaning1612 q) (meaning1634 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1612 = false ∨ valuation q 1634 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1635 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1635)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 6 10 (meaning1546 q) (meaning1613 q) (meaning1635 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1613 = false ∨ valuation q 1635 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1629)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 7 3 (meaning1547 q) (meaning1606 q) (meaning1629 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1606 = false ∨ valuation q 1629 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1630)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 7 4 (meaning1547 q) (meaning1607 q) (meaning1630 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1607 = false ∨ valuation q 1630 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1631)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 7 5 (meaning1547 q) (meaning1608 q) (meaning1631 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1608 = false ∨ valuation q 1631 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1632)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 7 6 (meaning1547 q) (meaning1609 q) (meaning1632 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1609 = false ∨ valuation q 1632 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1633)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 7 7 (meaning1547 q) (meaning1610 q) (meaning1633 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1610 = false ∨ valuation q 1633 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1634)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 7 8 (meaning1547 q) (meaning1611 q) (meaning1634 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1611 = false ∨ valuation q 1634 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1635 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1635)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 7 9 (meaning1547 q) (meaning1612 q) (meaning1635 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1612 = false ∨ valuation q 1635 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1630)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 8 3 (meaning1548 q) (meaning1606 q) (meaning1630 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1606 = false ∨ valuation q 1630 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1631)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 8 4 (meaning1548 q) (meaning1607 q) (meaning1631 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1607 = false ∨ valuation q 1631 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1632)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 8 5 (meaning1548 q) (meaning1608 q) (meaning1632 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1608 = false ∨ valuation q 1632 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1633)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 8 6 (meaning1548 q) (meaning1609 q) (meaning1633 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1609 = false ∨ valuation q 1633 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E020.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112020
