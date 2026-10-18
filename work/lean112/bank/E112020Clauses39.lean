import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1634)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 8 7 (meaning1548 q) (meaning1610 q) (meaning1634 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1610 = false ∨ valuation q 1634 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1635 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1635)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 8 8 (meaning1548 q) (meaning1611 q) (meaning1635 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1611 = false ∨ valuation q 1635 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1631)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 9 3 (meaning1549 q) (meaning1606 q) (meaning1631 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1606 = false ∨ valuation q 1631 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1632)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 9 4 (meaning1549 q) (meaning1607 q) (meaning1632 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1607 = false ∨ valuation q 1632 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1633)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 9 5 (meaning1549 q) (meaning1608 q) (meaning1633 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1608 = false ∨ valuation q 1633 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1634)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 9 6 (meaning1549 q) (meaning1609 q) (meaning1634 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1609 = false ∨ valuation q 1634 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1635 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1635)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 9 7 (meaning1549 q) (meaning1610 q) (meaning1635 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1610 = false ∨ valuation q 1635 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1632)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 10 3 (meaning1550 q) (meaning1606 q) (meaning1632 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1606 = false ∨ valuation q 1632 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1633)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 10 4 (meaning1550 q) (meaning1607 q) (meaning1633 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1607 = false ∨ valuation q 1633 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1634)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 10 5 (meaning1550 q) (meaning1608 q) (meaning1634 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1608 = false ∨ valuation q 1634 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1635 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1635)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 10 6 (meaning1550 q) (meaning1609 q) (meaning1635 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1609 = false ∨ valuation q 1635 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1636 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 10 7 (meaning1550 q) (meaning1610 q) (meaning1636 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1610 = false ∨ valuation q 1636 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) + (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (l₂ := [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1633)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27]) (countLit q [-29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (count1620 q) 11 3 (meaning1551 q) (meaning1606 q) (meaning1633 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1606 = false ∨ valuation q 1633 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1643)) (countLit q [-58]) (countLit q [-60]) (count1643 q) 1 (meaningNeg60 q) (meaning1643 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1643 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1643)) (countLit q [-58]) (countLit q [-60]) (count1643 q) 1 (meaningNeg58 q) (meaning1643 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1643 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 60 = true ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (1644)) (countLit q [-58]) (countLit q [-60]) (count1643 q) 1 1 (meaningNeg58 q) (meaningNeg60 q) (meaning1644 q) hs
  change (! (valuationOf q 58)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 1644 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-61]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (1645)) (countLit q [-61]) (countLit q [-65]) (count1645 q) 1 (meaningNeg65 q) (meaning1645 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1645 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-61]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1645)) (countLit q [-61]) (countLit q [-65]) (count1645 q) 1 (meaningNeg61 q) (meaning1645 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1645 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 65 = true ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-61]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-65])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-65)) (literal (valuationOf q) (1646)) (countLit q [-61]) (countLit q [-65]) (count1645 q) 1 1 (meaningNeg61 q) (meaningNeg65 q) (meaning1646 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 65)) = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 65 = true ∨ valuation q 1646 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1647)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 1 (meaning1645 q) (meaning1647 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1647 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_right (literal (valuationOf q) (1646)) (literal (valuationOf q) (1648)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 2 (meaning1646 q) (meaning1648 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1648 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 1 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1648)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 1 1 (meaning1643 q) (meaning1645 q) (meaning1648 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1645 = false ∨ valuation q 1648 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1649)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 1 2 (meaning1643 q) (meaning1646 q) (meaning1649 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1646 = false ∨ valuation q 1649 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_left (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 2 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1649)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 2 1 (meaning1644 q) (meaning1645 q) (meaning1649 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1645 = false ∨ valuation q 1649 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1650 = true := by
  have hs : count1647 q = (countLit q [-58, -60]) + (countLit q [-61, -65]) := List.countP_append (p := literal q) (l₁ := [-58, -60]) (l₂ := [-61, -65])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1650)) (countLit q [-58, -60]) (countLit q [-61, -65]) (count1647 q) 2 2 (meaning1644 q) (meaning1646 q) (meaning1650 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1646 = false ∨ valuation q 1650 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1651)) (countLit q [-66]) (countLit q [-68]) (count1651 q) 1 (meaningNeg68 q) (meaning1651 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1651 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1651)) (countLit q [-66]) (countLit q [-68]) (count1651 q) 1 (meaningNeg66 q) (meaning1651 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1651 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1652)) (countLit q [-66]) (countLit q [-68]) (count1651 q) 1 1 (meaningNeg66 q) (meaningNeg68 q) (meaning1652 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 1652 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1653)) (countLit q [-69]) (countLit q [-73]) (count1653 q) 1 (meaningNeg73 q) (meaning1653 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1653 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1653)) (countLit q [-69]) (countLit q [-73]) (count1653 q) 1 (meaningNeg69 q) (meaning1653 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1653 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E020.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112020
