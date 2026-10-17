import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1630)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 4 7 (meaning1544 q) (meaning1610 q) (meaning1630 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1610 = false ∨ valuation q 1630 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1631)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 4 8 (meaning1544 q) (meaning1611 q) (meaning1631 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1611 = false ∨ valuation q 1631 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1632)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 4 9 (meaning1544 q) (meaning1612 q) (meaning1632 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1612 = false ∨ valuation q 1632 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1627 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1627)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 3 (meaning1545 q) (meaning1606 q) (meaning1627 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1606 = false ∨ valuation q 1627 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1628 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1628)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 4 (meaning1545 q) (meaning1607 q) (meaning1628 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1607 = false ∨ valuation q 1628 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1629)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 5 (meaning1545 q) (meaning1608 q) (meaning1629 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1608 = false ∨ valuation q 1629 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1630)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 6 (meaning1545 q) (meaning1609 q) (meaning1630 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1609 = false ∨ valuation q 1630 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1631)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 7 (meaning1545 q) (meaning1610 q) (meaning1631 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1610 = false ∨ valuation q 1631 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1632)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 8 (meaning1545 q) (meaning1611 q) (meaning1632 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1611 = false ∨ valuation q 1632 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1633)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 9 (meaning1545 q) (meaning1612 q) (meaning1633 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1612 = false ∨ valuation q 1633 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1634)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 5 10 (meaning1545 q) (meaning1613 q) (meaning1634 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1613 = false ∨ valuation q 1634 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1628 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1628)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 6 3 (meaning1546 q) (meaning1606 q) (meaning1628 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1606 = false ∨ valuation q 1628 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1629)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 6 4 (meaning1546 q) (meaning1607 q) (meaning1629 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1607 = false ∨ valuation q 1629 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1630)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 6 5 (meaning1546 q) (meaning1608 q) (meaning1630 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1608 = false ∨ valuation q 1630 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1631)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 6 6 (meaning1546 q) (meaning1609 q) (meaning1631 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1609 = false ∨ valuation q 1631 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1632)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 6 7 (meaning1546 q) (meaning1610 q) (meaning1632 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1610 = false ∨ valuation q 1632 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1633)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 6 8 (meaning1546 q) (meaning1611 q) (meaning1633 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1611 = false ∨ valuation q 1633 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1634)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 6 9 (meaning1546 q) (meaning1612 q) (meaning1634 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1612 = false ∨ valuation q 1634 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1629 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1629)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 7 3 (meaning1547 q) (meaning1606 q) (meaning1629 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1606 = false ∨ valuation q 1629 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1630 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1630)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 7 4 (meaning1547 q) (meaning1607 q) (meaning1630 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1607 = false ∨ valuation q 1630 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1631)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 7 5 (meaning1547 q) (meaning1608 q) (meaning1631 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1608 = false ∨ valuation q 1631 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1632)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 7 6 (meaning1547 q) (meaning1609 q) (meaning1632 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1609 = false ∨ valuation q 1632 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1633)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 7 7 (meaning1547 q) (meaning1610 q) (meaning1633 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1610 = false ∨ valuation q 1633 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1634)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 7 8 (meaning1547 q) (meaning1611 q) (meaning1634 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1611 = false ∨ valuation q 1634 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1631 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1631)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 8 4 (meaning1548 q) (meaning1607 q) (meaning1631 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1607 = false ∨ valuation q 1631 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1632 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1632)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 8 5 (meaning1548 q) (meaning1608 q) (meaning1632 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1608 = false ∨ valuation q 1632 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1633 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1633)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 8 6 (meaning1548 q) (meaning1609 q) (meaning1633 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1609 = false ∨ valuation q 1633 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1634 = true := by
  have hs : count1620 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) + (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (l₂ := [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1634)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (count1620 q) 8 7 (meaning1548 q) (meaning1610 q) (meaning1634 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1610 = false ∨ valuation q 1634 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1643)) (countLit q [-60]) (countLit q [-62]) (count1643 q) 1 (meaningNeg62 q) (meaning1643 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1643 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1643)) (countLit q [-60]) (countLit q [-62]) (count1643 q) 1 (meaningNeg60 q) (meaning1643 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1643 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1644)) (countLit q [-60]) (countLit q [-62]) (count1643 q) 1 1 (meaningNeg60 q) (meaningNeg62 q) (meaning1644 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 1644 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1645)) (countLit q [-65]) (countLit q [-66]) (count1645 q) 1 (meaningNeg66 q) (meaning1645 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1645 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E186.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112186
